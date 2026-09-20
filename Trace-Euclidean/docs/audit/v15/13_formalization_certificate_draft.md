# Formalization certificate draft: scoped Grade B

Paper: Trace-Euclidean v15, author-source SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.

Formal package: PaperVerification/Trace-Euclidean/lean, Lean 4.32.1, pinned mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6. The general-radius and rank-one bridge update is identified by the repository revision carrying V15PropositionSixOne.lean.

Reviewed results: Theorems 1.2, 1.3, 1.7, and Corollary 1.9. Four PROVISIONAL_MATCH; zero VERIFIED_MATCH; zero identified critical semantic mismatches. Theorem 1.7 covers all nonzero fractional-ideal presentations and both directions of the six-class classification. Theorem 1.2/1.3 finiteness conclusions depend explicitly on Odlyzko's unconditional Table 4 input.

Proof trust: Lean kernel and pinned mathlib; standard logical axioms propext, Classical.choice, and Quot.sound. No project axiom or unfinished proof was found in the checked sources. Computation trusts Python, Wolfram, and extracted inputs; private source binding checks the author file.

Exclusions: independent human approval, a single bundled endpoint for Proposition 6.1's two integer-scalar specializations, all standalone supporting lemmas, historical and novelty claims, and proof of the cited Odlyzko theorem inside Lean. The generic Proposition 6.1 formula and canonical rank-one ideal bridge are proved.

Reproducibility: the bridge update passed a complete local Lean build and the expanded transitive-axiom audit. The previously published baseline passed public Lean, Python, axiom, clean-tree, and manuscript-exclusion gates at https://github.com/hzldew-git/PaperVerification/actions/runs/35520676689. The bridge revision is subject to the same clean-checkout workflow with 89 endpoint checks; its run status is shown at https://github.com/hzldew-git/PaperVerification/actions/workflows/lean.yml. Independently operated reproduction remains pending.

Assessment: Grade B for a substantial, scoped, reviewable formalization; this is not a certificate of complete manuscript correctness or Grade A semantic sign-off.
