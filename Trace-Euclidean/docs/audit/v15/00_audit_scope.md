# Audit scope: Trace-Euclidean v15

- Audit date: 2026-09-21 (bridge update to the 2026-09-20 audit).
- Frozen author source: Trace-Euclidean-v15.tex, SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
- Formal project: PaperVerification/Trace-Euclidean/lean; formalization commit ee76166c5f99eacd005d23efa6f3978dc6ae5d29 includes the general-radius, rank-one ideal, Proposition 6.1, cross-field transport, and finite-table modules. The earlier v15 baseline was code commit f3f8649c5f0e3820b8bbdc5216f44eb6d3df8edf.
- Proof assistant: Lean 4.32.1 with mathlib revision 520045ab14e26149ee970e2e617ca04b09bde5d6.
- Main results reviewed: Theorems 1.2, 1.3, and 1.7, plus Corollary 1.9. Corollary 1.6, all clauses of Proposition 6.1, abstract-space transport over arbitrary totally real fields, the rank-one ideal presentation, and the Section 4 finite-table consequences now have additional formal endpoints, pending independent semantic review.
- Evidence: independently extracted manuscript claims, elaborated Lean signatures, transitive axiom report, source-bound Python and Wolfram computations, public reruns, and adversarial semantic review.

The manuscript TeX and PDF remain outside the public repository. This is a first-party audit of the identified version. It does not certify historical claims, independent peer review, or every supporting lemma. The scoped project assessment is Grade B.
