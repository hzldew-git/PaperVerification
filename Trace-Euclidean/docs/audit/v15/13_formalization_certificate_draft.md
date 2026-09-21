# Formalization certificate draft: scoped Grade B

Paper: Trace-Euclidean v15, author-source SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.

Formal package: PaperVerification/Trace-Euclidean/lean, Lean 4.32.1, pinned mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6. The current update adds full cross-field lattice transport and finite Section 4 table theorems to the arbitrary-threshold rank-one, integer-scalar radius, and p-norm modules.

Reviewed results: Theorems 1.2, 1.3, 1.7, and Corollary 1.9. Four PROVISIONAL_MATCH; zero VERIFIED_MATCH; zero identified critical semantic mismatches. Theorem 1.7 covers all nonzero fractional-ideal presentations and both directions of the six-class classification. Theorem 1.2/1.3 finiteness conclusions depend explicitly on Odlyzko's unconditional Table 4 input.

Proof trust: Lean kernel and pinned mathlib; standard logical axioms propext, Classical.choice, and Quot.sound. No project axiom or unfinished proof was found in the checked sources. Computation trusts Python, Wolfram, and extracted inputs; private source binding checks the author file.

Additional formalized results: Corollary 1.6 for every finite p >= 1 and p = infinity; all clauses of Proposition 6.1 in one combined endpoint; actual scalar-field, space, lattice, and form transport for every positive-rank abstract lattice over any totally real field; the corresponding abstract rank-one ideal presentation; and all finite rank/degree maxima extracted from the Section 4 tables. These still require independent semantic sign-off.

Exclusions: independent human approval, selected standalone supporting lemmas, historical and novelty claims, proof of the cited Odlyzko theorem inside Lean, and a Lean proof that the public rational intervals classify every analytic H(n,d) grid cell. The finite table maxima themselves and cross-field lattice transport are now formalized.

Reproducibility: formalization commit ee76166c5f99eacd005d23efa6f3978dc6ae5d29 passed a complete local Lean build and the expanded 105-endpoint transitive-axiom audit; four additional finite-array equalities are axiom-free kernel computations. Fresh GitHub Actions runs then passed the public Lean build, forbidden-source scan, axiom audit, Python rerun, clean-tree gate, and manuscript-exclusion gate at https://github.com/hzldew-git/PaperVerification/actions/runs/35581394526 and https://github.com/hzldew-git/PaperVerification/actions/runs/35581394493. Independently operated reproduction remains pending.

Assessment: Grade B for a substantial, scoped, reviewable formalization; this is not a certificate of complete manuscript correctness or Grade A semantic sign-off.
