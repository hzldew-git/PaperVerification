# Reproducibility report

- The private author source and private frozen copy both have SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
- The private source-bound Python run produced 1165 PASS and 0 FAIL. Its Wolfram run produced 112 PASS and 0 FAIL.
- The public extracted-input Python and Wolfram checks were rerun after the current Lean update and produced 1156 PASS and 115 PASS, respectively, with 0 FAIL.
- The v15 Lean project completed a full local lake build on Lean 4.32.1 and pinned mathlib after adding the general-radius, rank-one threshold, scalar-radius, and p-norm modules. The expanded public MainTheoremAudit command printed 95 endpoint axiom sets, each with only standard Lean logical axioms.
- The subsequent abstract-coordinate update completed another local Lean build. The public MainTheoremAudit now prints 99 endpoint axiom sets, each with only propext, Classical.choice, and Quot.sound. It adds an actual isometry for any abstract positive-rank lattice over an already coded field, the abstract rank-one ideal bridge, and a code for every totally real number field preserving its integer ring and rational trace. Quadratic-space/lattice transport along the field isomorphism is not claimed.
- The original v15 formal baseline was code commit f3f8649c5f0e3820b8bbdc5216f44eb6d3df8edf. Formalization commit 741dc24cf0d41454116ff83c7295af31ff74ba76 contains the current rank-one threshold, scalar-radius, and p-norm bridges.
- The public verification package contains extracted inputs and scripts, not the manuscript. The old v9 result summary and verification manual are clearly labeled historical.
- GitHub Actions rebuilt formalization commit 741dc24cf0d41454116ff83c7295af31ff74ba76 in a fresh Ubuntu checkout and passed the Lean build, forbidden-construct scan, 95 endpoint axiom checks, v15 Python rerun, clean-tree gate, and manuscript-exclusion gate. The successful runs are https://github.com/hzldew-git/PaperVerification/actions/runs/35542188896 and https://github.com/hzldew-git/PaperVerification/actions/runs/35542188716. Independently operated reproduction and human semantic sign-off remain outstanding.

The reruns reproduce encoded statements and arithmetic under a fixed source version; they do not establish that every sentence of the manuscript is correct.
