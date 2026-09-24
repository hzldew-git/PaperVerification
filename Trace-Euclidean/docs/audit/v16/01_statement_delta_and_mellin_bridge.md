# v16 statement delta and Mellin bridge (24 September 2026)

**Later formalization update:** The field-specific theta/Mellin identities
and entire Gamma normalization described below as pending have since been
proved for every number field in the v15 verification code. See
[the zeta-continuation construction](../v15/20_zeta_continuation_construction.md).
The completed-zeta functional equation, circle-growth bound, and Stark/Weil
formula remain open. The v16 statement comparison below was not rerun for
this Lean-only update.

## Version comparison

The local author files compared were `Trace-Euclidean-v15.tex` (SHA-256
`83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5`)
and `Trace-Euclidean-v16.tex` (SHA-256
`b05b8aa6e646d5a248ef8914b2b017280411a4cdbbb31c26cfbff450ddaa44eb`).
Neither source file is included in this public repository. To repeat the
comparison on local copies, run
`python tools/compare_statement_environments.py PATH_TO_V15.tex PATH_TO_V16.tex`.

The check found 20 labelled theorem-like environments in each version. All 19
theorem, corollary, proposition, lemma, and definition bodies have identical
text after removing labels and normalizing whitespace. Remark `re:finiteness`
has editorial differences: “Q-isomorphism classes” became “isomorphism
classes of totally real number fields”, and the tables and references were
rephrased. Its numerical ranges and assertions did not change on manual
review. The rank-one thin-ideal paragraph was clarified in v16: the rank-one
and integrality assumptions, the positive integer norm, and the cited lemmas
are now stated separately. The displayed inequality is unchanged. The
quadratic-basis formula received an equation label, with a later reference
replacing a repeated display; the formula is unchanged.

This is a statement-drift check, not a proof of every sentence or a fresh
human sign-off. The existing v15 formal theorems can be cited as evidence for
the unchanged v16 main statements at the same conditional scope. The four
main-result assessments remain `PROVISIONAL_MATCH`, with no independent
`VERIFIED_MATCH`. Proof prose, all uncaptured unlabelled assertions, and the
external-source premises require separate mathematical review. If the author
edits v16 again, rerun the comparison against the new SHA-256.

## New abstract analytic proof

The Apache-2.0 module
[`AnalyticMellinPrinciple.lean`](../../lean/TraceEuclidean/AnalyticMellinPrinciple.lean)
was adapted from
[`mathlib-initiative/sum_product`, commit `80e4127`](https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/MellinPrinciple.lean).
The source pins Lean/mathlib `v4.31.0-rc1`; the isolated module compiles under
this project's Lean 4.32.1 and pinned mathlib after removal of one redundant
tactic. The source
license is copied to
[`sum_product_APACHE-2.0.txt`](../../lean/THIRD_PARTY_LICENSES/sum_product_APACHE-2.0.txt).
The imported theorems prove convergence on `Re(s)>k`, entire analyticity of
the Mellin tail, and agreement of the continuation expression with the
original reduced Mellin integral there.

[`V15AnalyticMellinBridge.lean`](../../lean/TraceEuclidean/V15AnalyticMellinBridge.lean)
adds proofs that the polynomial pole removal is entire, agrees with the
meromorphic expression away from `0,k`, and satisfies the reflection equation
on all of `ℂ`; the meromorphic expression also satisfies its functional
equation away from the poles. A normalization-factor interface constructs the
existing `V15DedekindZetaRegularization` once a field-specific entire factor
and the right-half-plane theta-to-zeta identity are supplied. These are
genuine remaining premises, not definitions that assert the desired theorem.

The source project retains theta inversion and partial-zeta Mellin code, but
its exported [`ConeMellinBridge.lean`](https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/ConeMellinBridge.lean)
explicitly stops before the final all-field meromorphic continuation and
functional-equation assembly. The remaining work is to prove the number-field
theta/Poisson hypotheses, the precise gamma and discriminant normalization,
and the right-half-plane identification with mathlib's Dedekind zeta. A
growth bound for the resulting entire function and the Stark/Weil explicit
formula are further independent tasks.

## Numerical trust

The `A,B` integral certificate continues to use LeanCert and four
`native_decide` invocations in `V15OdlyzkoNumerical.lean`; an Euler--Mascheroni
bound used by that certificate contributes another generated native axiom.
This is native-compiler trust, disclosed separately in `TRUST.md` and the
numerical axiom audit. The new Mellin declarations use only the standard
logical axioms. A kernel-only numerical certificate would require replacing
these computations and rerunning the transitive axiom audit; no such claim is
made here.
