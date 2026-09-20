# Reproducibility report

- The private author source and private frozen copy both have SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
- The private source-bound Python run produced 1165 PASS and 0 FAIL. Its Wolfram run produced 112 PASS and 0 FAIL.
- The public extracted-input Python run produced 1156 PASS and 0 FAIL. Its Wolfram run produced 115 PASS and 0 FAIL.
- The v15 Lean project completed a full lake build on Lean 4.32.1 and pinned mathlib. The public MainTheoremAudit command printed the new classification, representative, and finiteness signatures, each with only standard Lean logical axioms.
- The public verification package contains extracted inputs and scripts, not the manuscript. The old v9 result summary and verification manual are clearly labeled historical.
- A fresh independent-machine build and human semantic sign-off remain outstanding. GitHub push state is reported in the release note after deployment is attempted.

The reruns reproduce encoded statements and arithmetic under a fixed source version; they do not establish that every sentence of the manuscript is correct.
