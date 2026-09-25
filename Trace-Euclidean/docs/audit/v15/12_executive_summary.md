# Executive summary

Zeta-continuation update: the vendored number-field theta/Poisson and Mellin
modules now prove an entire continuation of `(s-1) ζ_K(s)` for every number
field and instantiate `V15DedekindZetaRegularization`. The right-half-plane
identity and the entire reciprocal Gamma normalization are Lean theorems.
The completed-zeta functional equation and a global quadratic exponential
growth bound are now proved in Lean. The latter supplies the Jensen circle
bound, a quadratic count of actual zero occurrences, and absolute convergence
of their direct Odlyzko transform. The Stark/Weil formula remains open. See
[the construction note](20_zeta_continuation_construction.md). The four main
results remain PROVISIONAL_MATCH.

Jensen update: Lean derives a quadratic count of actual critical-strip zero
occurrences from the proved quadratic exponential growth bound for the
constructed entire completed zeta. This gives absolute convergence and a
nonnegative real part for the direct zero sum without the sharp HSW numerical
count. The Stark/Weil explicit formula remains unproved.
The four PROVISIONAL_MATCH
assessments and Grade B boundary are unchanged.

Archimedean update: Lean now starts from the actual completed-zeta Gamma
factor, proves joint absolute integrability with the critical transform,
justifies both Gauss-digamma Fubini interchanges and the real-place variable
change, and derives exactly
`log |D_K| - r_1 log A_* - 2 r_2 log B_*`. The remaining explicit-formula
boundary consists of the transformed prime-power matching and the global
contour/residue identity.

Paper version: Trace-Euclidean v15, SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5. Proof assistant: Lean 4.32.1 with pinned mathlib. Project assessment: SUBSTANTIAL_FORMALIZATION, Grade B.

The three main theorems and field corollary have version-specific Lean evidence. The two global theorems prove strict root-discriminant bounds and varying-degree finiteness from the cited unconditional Odlyzko Table 4 row. The literature-facing Lean interface retains the signature exponents and nonnegative prime-ideal correction, proves the upward rounding of the error term and the totally real specialization, and requires the row only from degree fifteen. The source's unconditional `b=4` kernel is formalized with proofs of evenness, nonnegativity, continuity, compact support, integrability, and global differentiability. Lean verifies exponential decay of `F` and `F'` outside the support, derives the exact archimedean error integral `E = 32/3`, and proves `Phi(0) = Phi(1) = 16/3` and `Phi(0) + Phi(1) = 32/3`. It identifies `H` as a normalized autocorrelation, evaluates the exact hyperbolic-secant and tilted transforms, and proves `Re Phi(s) >= 0` for every `0 <= Re(s) <= 1`, including both boundary lines. Lean proves that `Phi` is entire, differentiates its defining integral, shows qualitative decay on every fixed vertical line, establishes the exact conjugate-pair identities and paired-series summability equivalence, and derives summability from explicit count and decay bounds. The complete prime-ideal correction is proved equal to a finite box with norm at most 4095 and exponent at most eleven, and is nonnegative. The two archimedean integrals are proved convergent, and strict `A,B` bounds are supplied by analytic endpoint estimates and certified dyadic checks. A conditional source-formula theorem derives the Table 4 interface from equation (2.3), the now-proved integral certificate, and convergent real-zero terms and distinct nonreal conjugate-pair terms. The rank-one classification is a two-direction theorem over every nonzero fractional-ideal presentation, including an actual isometry to one of six free forms; the six forms are valid, strictly trace Euclidean, and distinct. The field-square corollary remains an exact concrete iff theorem.

All four reviewed main results are PROVISIONAL_MATCH; none is independently VERIFIED_MATCH. Proposition 6.1 has one combined endpoint containing the generic radius and determinant for every qualifying real-quadratic fractional ideal and both positive-integer scalar formulas on the full integer ring. An actual semilinear isometry transports any abstract positive-rank lattice over any totally real number field to a coded canonical coordinate model, preserving the full lattice, quadratic form, trace Euclideanity, degree, and classic integrality; rank one composes to an ideal presentation at any real threshold. Lean evaluates the exact Section 4 quantity H(n,d), proves rational enclosures, and checks that its two analytic inequalities select exactly the frozen 24 classic and 63 integral pairs on the full 34 by 14 grid. It proves the degree-one discriminant input from Minkowski and derives class-level table membership from source-specific premises for degrees 2--9, degree 10, degree 11, and Table 4 from degree 12. The online November 1976 Table 2 gives 14.034 at degree 11, so the v15 value 14.083 remains a separately cited later optimized bound. Corollary 1.6 has a varying-field finiteness endpoint for every finite p >= 1 and p = infinity. Lean proves global `C^4` regularity of the exact Odlyzko kernel, uniform fourth-power transform decay throughout the closed critical strip, and absolute summability of the direct zero-occurrence sum. It also proves that any entire continuation of `(s-1) ζ_K(s)` is unique, nonzero, and conjugation symmetric, and that its multiplicity-aware strip-zero occurrences are finite at bounded height and are paired by a height-preserving conjugation involution. The completed Dedekind-zeta functional equation is proved by trace-dual ideal rescaling and class-group reindexing. Theta decay and Mellin-tail estimates give the completed function a global quadratic exponential bound; Jensen then gives a quadratic count for actual zero occurrences and convergence of the direct zero sum. Remaining limits include the cited degree 2--11 discriminant results, the Stark/Weil explicit formula, selected standalone supporting lemmas, and unsigned author/domain/Lean review cards.

A finite-height exhaustion proves that multiplicity-aware strip-zero occurrences are countable. After every height there is a right interval with constant zero count. For the exact HSW Corollary 1.2 normalization, Lean extends an inequality assumed at occurrence-free heights to every T >= 1. That sharp inequality remains an explicit input but is unnecessary for the completed-function Jensen route. The direct unordered zero sum now converges from the internally proved quadratic count. The HSW Gamma factor has been matched to mathlib, with critical-strip zero positions and analytic multiplicities preserved by completion. The completed-zeta functional equation and sufficient growth bound are proved. The Stark/Weil explicit formula remains unproved. The source map is in 18_classical_analytic_sources.md.

The complete local 8817-job Lean build passes. The expanded axiom audit includes the constructed zeta regularization, functional equation, Mellin growth, Jensen, zero-count, unordered-zero, and archimedean Fubini endpoints using only standard logical axioms; the final reduction also exposes the A/B interval certificate's separately disclosed native-compiler trust. The four finite-array equality proofs are kernel computations with no axiom dependencies. Local public reruns produced 1156 Python PASS and 115 Wolfram PASS, both with zero failures. Superseded release evidence is not included in the current package or v15 counts.
