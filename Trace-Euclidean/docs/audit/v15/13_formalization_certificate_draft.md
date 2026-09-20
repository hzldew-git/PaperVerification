# Formalization certificate draft: scoped Grade B

Paper: Trace-Euclidean v15, author-source SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.

Formal package: PaperVerification/Trace-Euclidean/lean, Lean 4.32.1, pinned mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6. The current update adds arbitrary-threshold rank-one, integer-scalar radius, and p-norm modules.

Reviewed results: Theorems 1.2, 1.3, 1.7, and Corollary 1.9. Four PROVISIONAL_MATCH; zero VERIFIED_MATCH; zero identified critical semantic mismatches. Theorem 1.7 covers all nonzero fractional-ideal presentations and both directions of the six-class classification. Theorem 1.2/1.3 finiteness conclusions depend explicitly on Odlyzko's unconditional Table 4 input.

Proof trust: Lean kernel and pinned mathlib; standard logical axioms propext, Classical.choice, and Quot.sound. No project axiom or unfinished proof was found in the checked sources. Computation trusts Python, Wolfram, and extracted inputs; private source binding checks the author file.

Additional formalized results: Corollary 1.6 for every finite p >= 1 and p = infinity, and all clauses of Proposition 6.1 in one combined endpoint. Both still require independent semantic sign-off.

Exclusions: independent human approval, all standalone supporting lemmas and numerical table maxima, historical and novelty claims, and proof of the cited Odlyzko theorem inside Lean. The abstract-to-canonical model equivalence remains a review item.

Reproducibility: the current update passed a complete local Lean build and the expanded 95-endpoint transitive-axiom audit. Published bridge release ec2b406 passed public Lean, Python, axiom, clean-tree, and manuscript-exclusion gates at https://github.com/hzldew-git/PaperVerification/actions/runs/35523843755. Consult https://github.com/hzldew-git/PaperVerification/actions/workflows/lean.yml for the current revision's clean-checkout status. Independently operated reproduction remains pending.

Assessment: Grade B for a substantial, scoped, reviewable formalization; this is not a certificate of complete manuscript correctness or Grade A semantic sign-off.
