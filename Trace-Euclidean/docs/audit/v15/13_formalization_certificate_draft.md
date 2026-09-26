# Formalization certificate draft: scoped Grade B

Paper: Trace-Euclidean v15, author-source SHA-256
`83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5`.

Formal package: `PaperVerification/Trace-Euclidean/lean`, Lean 4.32.1,
mathlib v4.32.1.

## Reviewed results

The audit covers Theorems 1.2, 1.3, and 1.7, Corollaries 1.6 and 1.9, and
Proposition 6.1. All remain `PROVISIONAL_MATCH`; none is marked
`VERIFIED_MATCH` because the author/domain and independent Lean review cards
are unsigned. No identified critical semantic mismatch or hidden project
axiom remains.

Theorem 1.7 covers every nonzero fractional-ideal presentation and both
directions of the six-class classification. Corollary 1.6 covers every finite
`p >= 1` and `p = infinity`. Proposition 6.1 includes the general reduced
binary radius theorem, its actual-ideal transfer, and both integer-scalar
specializations. The abstract rank-one route transports arbitrary totally
real fields, spaces, full lattices, and forms to the coded model.

## Odlyzko and finiteness closure

The package constructs the pole-removed completed Dedekind zeta, proves its
functional equation and quadratic growth, counts actual zeros with
multiplicity, and controls its logarithmic derivative on zero-free contour
heights. A finite weighted argument principle, vanishing horizontal edges,
and a vertical limit then identify the specialized `b = 4` contour integral.
Lean evaluates the endpoint as `32/3`, the archimedean contribution as
`log |D_K| - r_1 log(A_*) - 2 r_2 log(B_*)`, and the ordinary-zeta
contribution as minus the complete prime correction. It proves
`v15Odlyzko_discriminant_log_lower_bound` and constructs the exact-error and
rounded Table 4 interfaces internally.

Consequently `v15_classic_finite_closed`, `v15_integral_finite_closed`, and
`v15_pnorm_finite_closed` do not assume Odlyzko's Table 4 theorem. The source
table remains essential for normalization and comparison. Degrees one through
four and the range from degree twelve are internal. In degree four, Lean proves
the projected Minkowski construction, transverse second-vector selection,
quartic normalization and order maximality, and the quadratic-subfield
compositum contradiction, yielding the unconditional bound `|D_K| >= 725`.
All 2,773 degree 5--10 Voight polynomial rows are imported and structurally
checked. Python and Mathematica independently verify their irreducibility,
total reality, discriminant-index equations, and field discriminants. Lean
bridges the exact equations to its Hunter filter as one precisely named
input. Use of the degree 5--9 columns and the degree-ten exclusion is reduced
to one cited enumeration-completeness statement; the optimized degree-eleven
bound remains a separate input.
The latter is stated in the all-degrees form quoted by Voight and specialized
to Section 4 in Lean. An exact sensitivity theorem proves that the online
Table 2 value `14.034` would add the integral-table cell `(2,11)`, while the
manuscript's `14.083` excludes it.

## Trust

The analytic contour core depends only on Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. No checked `.lean` source uses
`sorry`, `sorryAx`, or a project axiom. The strict `A = 36.347` and
`B = 16.593` certificate uses `native_decide`; its five generated native
dependencies form a separately disclosed compiler trust boundary. The
The two Voight finite-data certificates add two separately audited native
dependencies.

Python and Wolfram checks trust their respective runtimes and the extracted
inputs. Private source binding checks the author-source hash. Successful
compilation and computation do not by themselves certify semantic fidelity.

## Exclusions

The certificate excludes independent human approval, historical and novelty
claims, Lean-kernel proofs of the concrete Voight polynomial-discriminant
equations and enumeration completeness, the optimized degree-eleven
field-discriminant estimate, the
optional sharper HSW numerical zero-count theorem, and selected standalone
supporting lemmas that are not needed by the audited endpoints. It does not
claim a general reusable Stark--Weil theorem for arbitrary test functions;
the proved result is the specialized unconditional `b = 4` inequality needed
by this manuscript.

## Reproducibility

The pinned toolchain is recorded in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. The current build, transitive axiom audits, manuscript
exclusion guard, and public computation reruns are recorded in
`11_reproducibility_report.md`. A Lean or mathlib upgrade requires a separate
full migration build and does not alter the validity of the reproducible
4.32.1 snapshot.

Assessment: Grade B for a substantial, scoped, reviewable formalization. This
is not a certificate of complete manuscript correctness or Grade A semantic
sign-off.
