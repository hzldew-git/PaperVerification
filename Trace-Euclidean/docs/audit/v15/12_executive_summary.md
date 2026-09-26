# Executive summary

Contour-closure update: Lean now proves the finite weighted argument principle
for the pole-removed completed Dedekind zeta, constructs expanding zero-free
rectangles, proves the horizontal sides vanish, and passes the folded vertical
integral to the limit. The endpoint polynomial contributes exactly `32/3`;
the archimedean line shift gives
`log |D_K| - r_1 log A_* - 2 r_2 log B_*`; and the ordinary zeta term is minus
the complete prime correction. Positivity of each finite zero sum therefore
gives the exact logarithmic discriminant lower bound. Together with the
certified strict `A,B` estimates, Lean constructs both the exact-error and
rounded Table 4 inputs and the classic, integral, and power-mean finiteness
endpoints without a Table 4 hypothesis. See
[the contour-closure note](22_odlyzko_contour_closure.md). The four main
results remain PROVISIONAL_MATCH pending independent semantic review.

Jensen update: Lean derives a quadratic count of actual critical-strip zero
occurrences from the proved quadratic exponential growth bound for the
constructed entire completed zeta. This gives absolute convergence and a
nonnegative real part for the direct zero sum without the sharp HSW numerical
count. The final contour proof uses finite nonnegative zero sums directly, so
it does not require an ordered zero enumeration or an infinite zero-sum
identity. The four PROVISIONAL_MATCH assessments and Grade B boundary are
unchanged.

Archimedean update: Lean now starts from the actual completed-zeta Gamma
factor, proves joint absolute integrability with the critical transform,
justifies both Gauss-digamma Fubini interchanges and the real-place variable
change, and derives exactly
`log |D_K| - r_1 log A_* - 2 r_2 log B_*`. The completed explicit-formula
work also includes arbitrary vertical-line fourth-power decay and Fourier
inversion, the exact transform of every prime-power Euler term, an absolutely
convergent sum/integral exchange, and the resulting actual Dedekind-zeta
logarithmic-derivative identity. The subsequent contour modules close the
global residue and limiting argument.

Paper version: Trace-Euclidean v15, SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5. Proof assistant: Lean 4.32.1 with pinned mathlib. Project assessment: SUBSTANTIAL_FORMALIZATION, Grade B.

The three main theorems and field corollary have version-specific Lean evidence. The two global theorems prove strict root-discriminant bounds and varying-degree finiteness from an internally constructed `b=4` inequality matching the cited unconditional Odlyzko Table 4 row. The literature-facing Lean interface retains the signature exponents and nonnegative prime-ideal correction, proves the upward rounding of the error term and the totally real specialization, and requires the row only from degree fifteen. The source's unconditional `b=4` kernel is formalized with proofs of evenness, nonnegativity, continuity, compact support, integrability, and global differentiability. Lean verifies exponential decay of `F` and `F'` outside the support, derives the exact archimedean error integral `E = 32/3`, and proves `Phi(0) = Phi(1) = 16/3` and `Phi(0) + Phi(1) = 32/3`. It identifies `H` as a normalized autocorrelation, evaluates the exact hyperbolic-secant and tilted transforms, and proves `Re Phi(s) >= 0` for every `0 <= Re(s) <= 1`, including both boundary lines. Lean proves that `Phi` is entire, differentiates its defining integral, shows qualitative decay on every fixed vertical line, establishes the exact conjugate-pair identities and paired-series summability equivalence, and derives summability from explicit count and decay bounds. The complete prime-ideal correction is proved equal to a finite box with norm at most 4095 and exponent at most eleven, and is nonnegative. The two archimedean integrals are proved convergent, and strict `A,B` bounds are supplied by analytic endpoint estimates and certified dyadic checks. The completed contour proof derives the Table 4 interface directly from finite nonnegative zero sums, the exact endpoint, archimedean, and prime transforms, and the expanding-rectangle limit. The rank-one classification is a two-direction theorem over every nonzero fractional-ideal presentation, including an actual isometry to one of six free forms; the six forms are valid, strictly trace Euclidean, and distinct. The field-square corollary remains an exact concrete iff theorem.

All four reviewed main results are PROVISIONAL_MATCH; none is independently VERIFIED_MATCH. Proposition 6.1 has one combined endpoint containing the generic radius and determinant for every qualifying real-quadratic fractional ideal and both positive-integer scalar formulas on the full integer ring. An actual semilinear isometry transports any abstract positive-rank lattice over any totally real number field to a coded canonical coordinate model, preserving the full lattice, quadratic form, trace Euclideanity, degree, and classic integrality; rank one composes to an ideal presentation at any real threshold. Lean evaluates the exact Section 4 quantity H(n,d), proves rational enclosures, and checks that its two analytic inequalities select exactly the frozen 24 classic and 63 integral pairs on the full 34 by 14 grid. The degree-one through degree-four discriminant bounds are internal. In degree four, an unconditional Minkowski construction supplies a first projected short vector and, if needed, a transverse second vector. A primitive lift is impossible by exact normalization, the six-row search, and maximality of the `2048` and `2304` power orders. If both lifts are imprimitive, their distinct quadratic subfields have discriminants in `{5,8}`. Equal discriminants force equality of the subfields, while unequal discriminants are coprime and force quartic discriminant `1600`. Thus `v15_coded_degree_four_discriminant_ge_725` has no source premise. The exact-minimum source inputs begin in degree five, followed by the degree-ten exclusion and optimized degree-eleven bound. The online November 1976 Table 2 gives 14.034 at degree 11, so the v15 value 14.083 remains a separately cited later optimized bound. Corollary 1.6 has a varying-field finiteness endpoint for every finite p >= 1 and p = infinity. The completed Dedekind-zeta continuation, functional equation, quadratic growth, Jensen count, zero-sum convergence, specialized contour formula, archimedean transform, and prime correction are proved. Remaining limits are the cited degree 5--11 discriminant results, selected standalone supporting lemmas, the disclosed native numerical certificate, and unsigned author/domain/Lean review cards.

A finite-height exhaustion proves that multiplicity-aware strip-zero occurrences are countable. After every height there is a right interval with constant zero count. For the exact HSW Corollary 1.2 normalization, Lean extends an inequality assumed at occurrence-free heights to every T >= 1. That sharp inequality remains an optional explicit input but is unnecessary for the completed-function Jensen and contour routes. The direct unordered zero sum converges from the internally proved quadratic count. The HSW Gamma factor has been matched to mathlib, with critical-strip zero positions and analytic multiplicities preserved by completion. The completed-zeta functional equation, sufficient growth bound, and specialized `b=4` contour inequality are proved. The source map is in 18_classical_analytic_sources.md.

The complete local 8870-job Lean build passes. The 494-declaration main axiom audit includes the unconditional quartic short-vector selection and lower bound; those new endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. Final endpoints that use the strict Odlyzko numerical certificate also show its five disclosed native-compiler dependencies. The separate 32-declaration numerical audit isolates the same boundary. The finite quartic searches use kernel `decide` and add no compiler trust. Local public reruns produced 1156 Python PASS and 115 Wolfram PASS, both with zero failures. The manuscript guard inspected 280 files and passed. Superseded release evidence is not included in the current package or v15 counts.
