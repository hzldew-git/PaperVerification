# Reproducibility report

- The private author source and private frozen copy both have SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
- The private source-bound Python run produced 1165 PASS and 0 FAIL. Its Wolfram run produced 112 PASS and 0 FAIL.
- The public extracted-input Python and Wolfram checks were rerun after the current Lean update and produced 1156 PASS and 115 PASS, respectively, with 0 FAIL.
- The v15 Lean project completed a full local lake build on Lean 4.32.1 and pinned mathlib after adding the general-radius, rank-one threshold, scalar-radius, and p-norm modules. The expanded public MainTheoremAudit command printed 95 endpoint axiom sets, each with only standard Lean logical axioms.
- The original v15 formal baseline was code commit f3f8649c5f0e3820b8bbdc5216f44eb6d3df8edf. The current bridge release is identified by the repository revision containing V15PropositionSixOne.lean.
- The public verification package contains extracted inputs and scripts, not the manuscript. The old v9 result summary and verification manual are clearly labeled historical.
- GitHub Actions rebuilt bridge release ec2b40620c7a14f1b0460ad16d46ead057dbdb06 in a fresh Ubuntu checkout and passed the Lean build, forbidden-construct scan, 89 endpoint axiom checks, v15 Python rerun, clean-tree gate, and manuscript-exclusion gate. The successful run is https://github.com/hzldew-git/PaperVerification/actions/runs/35523843755. The current 95-endpoint revision passed locally; consult https://github.com/hzldew-git/PaperVerification/actions/workflows/lean.yml for its clean-checkout status. Independently operated reproduction and human semantic sign-off remain outstanding.

The reruns reproduce encoded statements and arithmetic under a fixed source version; they do not establish that every sentence of the manuscript is correct.
