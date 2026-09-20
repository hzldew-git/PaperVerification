# Reproducibility report

- The private author source and private frozen copy both have SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
- The private source-bound Python run produced 1165 PASS and 0 FAIL. Its Wolfram run produced 112 PASS and 0 FAIL.
- The public extracted-input Python run produced 1156 PASS and 0 FAIL. Its Wolfram run produced 115 PASS and 0 FAIL.
- The v15 Lean project completed a full lake build on Lean 4.32.1 and pinned mathlib. The public MainTheoremAudit command printed the new classification, representative, and finiteness signatures, each with only standard Lean logical axioms.
- The fixed formal code commit is f3f8649c5f0e3820b8bbdc5216f44eb6d3df8edf. The later documentation-only release commit does not alter the Lean proofs.
- The public verification package contains extracted inputs and scripts, not the manuscript. The old v9 result summary and verification manual are clearly labeled historical.
- GitHub Actions rebuilt the published code in a fresh Ubuntu checkout and passed the Lean build, forbidden-construct scan, 84 endpoint axiom checks, v15 Python rerun, clean-tree gate, and manuscript-exclusion gate. The successful run is https://github.com/hzldew-git/PaperVerification/actions/runs/35520676689. Independently operated reproduction and human semantic sign-off remain outstanding.

The reruns reproduce encoded statements and arithmetic under a fixed source version; they do not establish that every sentence of the manuscript is correct.
