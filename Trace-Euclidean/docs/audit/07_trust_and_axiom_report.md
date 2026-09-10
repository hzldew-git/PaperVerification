# Trust and axiom report

## Lean evidence

- Toolchain: Lean 4.32.1.
- Dependency lock: `lake-manifest.json`, including mathlib revision
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- Full build: PASS, more than 8,600 Lake jobs.
- Forbidden-construct scan: PASS, zero matches.
- Audited endpoints: 40.
- Transitive axiom set for every endpoint:
  `propext`, `Classical.choice`, `Quot.sound`.

The scan rejects `sorry`, `sorryAx`, a project `axiom`, `native_decide`,
`run_tac`, `unsafe`, `extern`, and `implemented_by`. The complete public
signature and axiom output is in
`lean/audit/main_theorem_axioms.txt`.

`noncomputable section` declarations control executable code generation and
do not declare axioms. `MainFinitenessFramework` is also not an axiom: it is
an explicit theorem parameter. Its mathematical fields are therefore visible
in every affected endpoint signature and are assessed as stronger assumptions.

## Computational evidence

The final private maintainer run bound the package to the target manuscript
hash and produced `2165 PASS / 0 WARN / 0 FAIL`. It covered 15 displayed
numeric claims, 42 table rows, 12 maximum rows, 121 square-free parameters, and
22 Section 4 calculation groups.

The computational trust base includes the Wolfram kernel, the Python extraction
and reporting scripts, and the fidelity of the manifest to the displayed paper
formulas. Rational interval certificates and exact symbolic identities are
machine-checkable within that trust base; high-precision diagnostics are not
formal proofs of external analytic inequalities.

## What this report does not establish

No independent Lean kernel implementation, independent computer algebra
system, or independent human reviewer has signed this release. The evidence
does not validate cited external theorems or close the semantic gaps identified
in `05_theorem_correspondence.md`.
