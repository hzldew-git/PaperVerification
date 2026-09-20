# Trace-Euclidean v15: active Grade B assessment

Frozen author source SHA-256:
83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
The manuscript is excluded from this public repository.

The complete pinned Lean build passes. The v15 public Python and Wolfram
reruns pass 1156 and 115 checks, respectively; private source-bound reruns
pass 1165 and 112 checks. Audited Lean endpoints use only standard
logical axioms.
Formalization commit 741dc24 passed the [fresh GitHub Actions Lean, Python,
and 95-endpoint axiom run](https://github.com/hzldew-git/PaperVerification/actions/runs/35542188896)
and the [manuscript-exclusion run](https://github.com/hzldew-git/PaperVerification/actions/runs/35542188716).
The same formalization passed a complete local Lean build. Consult the
[Lean workflow](https://github.com/hzldew-git/PaperVerification/actions/workflows/lean.yml)
for later revisions' clean-checkout status.

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
semantic review. Transport from every abstract number-field lattice to the
canonical coordinate model and selected supporting numerical results remain
outside the current signed scope.

Start with [README.md](README.md), [THEOREM_INDEX.md](THEOREM_INDEX.md),
and the [v15 audit](docs/audit/v15/12_executive_summary.md).
The v9 package remains archived for version comparison.
