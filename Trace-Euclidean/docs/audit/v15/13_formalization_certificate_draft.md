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
table remains essential for normalization and comparison. The Section 4
class-level bridge still takes the cited degree `2`--`11` field-discriminant
estimates; degree one and the range from degree twelve are internal.

## Trust

The analytic contour core depends only on Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. No checked `.lean` source uses
`sorry`, `sorryAx`, or a project axiom. The strict `A = 36.347` and
`B = 16.593` certificate uses `native_decide`; its five generated native
dependencies form a separately disclosed compiler trust boundary.

Python and Wolfram checks trust their respective runtimes and the extracted
inputs. Private source binding checks the author-source hash. Successful
compilation and computation do not by themselves certify semantic fidelity.

## Exclusions

The certificate excludes independent human approval, historical and novelty
claims, proofs of the cited degree `2`--`11` field-discriminant estimates, the
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
