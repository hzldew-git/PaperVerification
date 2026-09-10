# Trace-Euclidean verification package

This directory is the public computational companion to the manuscript version
identified by the SHA-256 digest in `results/summary.json`. It contains
Mathematica verification, a Lean 4 formalization of selected proof obligations,
extracted numerical inputs, machine-readable results, certificates, an English
LaTeX manual, and a semantic-fidelity audit.

The manuscript source and rendered manuscript PDF are deliberately excluded.
They are neither required for rerunning the published calculations nor allowed
in this repository.

## Reproduce the published calculations

From PowerShell in this directory, run:

```powershell
& 'C:\Program Files\Wolfram Research\WolframScript\wolframscript.exe' -file '.\run_verification.wls'
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\build_report.py'
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\check_delivery.py'
```

Executable paths may be replaced with the corresponding local installations.
The Mathematica batch exit codes are `0` for all PASS, `2` for manuscript
presentation warnings with no failed verification check, and `1` for an exact,
certified, coverage, or integrity failure.

The public run uses `inputs/manuscript_inputs.json`, which records the source
SHA-256 digest, displayed numbering, stable LaTeX anchors, table entries, and
formula fragments extracted during the private maintainer build. Because the
manuscript itself is absent, the public run validates the calculations and the
internal correspondence of the published package; it does not recompute the
digest from a manuscript file.

## Reproduce the Lean formalization

The Lean project pins Lean and mathlib. From `lean/`, run:

```text
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
```

The final command prints 50 elaborated public signatures and their transitive
axiom sets. The formalization has no `sorry`, `sorryAx`, project `axiom`,
`native_decide`, `run_tac`, `unsafe`, `extern`, or `implemented_by`.

The concrete real-quadratic endpoint constructs
`QuadraticAlgebra ℚ m 0`, proves both integral-basis descriptions, transports
the trace-square cost to exact coordinates, proves the full-plane covering
formulas, and concludes
`IsFieldTraceEuclidean 2 ↔ m = 2 ∨ m = 5 ∨ m = 13`.
The eight finiteness endpoints preserve the paper's rank, degree, and
`t ≤ d` quantifiers on the actual quotient of field-lattice pairs. They are
unconditional Lean theorems: a projective pseudobasis proves the general
trace determinant and covolume bounds, Hermite gives bounded-discriminant
field finiteness, and finite reduction codes prove fixed-field, fixed-rank
lattice finiteness. See `THEOREM_INDEX.md` and `docs/audit/` for the remaining
semantic confirmation items and the Grade B assessment.

## Main deliverables

- `verify_trace_euclidean_v9.m`: interactive Mathematica entry point; it does
  not close the kernel.
- `run_verification.wls`: WolframScript wrapper with a batch exit code.
- `checks/`: focused modules for analytic bounds, admissible tables, trace
  geometry, and gamma diagnostics.
- `docs/verification_manual_v9.tex`: English LaTeX explanation and maintenance
  guide.
- `output/pdf/verification_manual_v9.pdf`: compiled verification manual with
  manuscript numbering and the complete Section 4 calculation ledger.
- `results/tests.json` and `results/tests.csv`: every check, with its module,
  manuscript location, evidence class, actual value, and status.
- `results/verification_ledger.json`: manuscript-to-code-to-result map.
- `results/section4_coverage.json`: all Mathematica-checkable Section 4
  calculations and their associated test records.
- `results/rational_certificates.json`: exact interval endpoints and certified
  signs.
- `results/all_table_values.csv`: values behind every admissible table pair.
- `SHA256SUMS.json`: hashes for the public code, inputs, results, logs, and
  verification documentation.
- `lean/`: pinned Lean 4 source, tests, and the public axiom report.
- `THEOREM_INDEX.md`: paper-to-Mathematica-to-Lean coverage map.
- `TRUST.md`: proof, computation, reproducibility, and semantic trust boundary.
- `docs/audit/`: English semantic-fidelity review package.

## Maintainer update after a manuscript revision

Keep the revised manuscript outside this Git repository, then run:

```powershell
.\build_all.ps1 -ManuscriptPath 'D:\private\path\Trace-Euclidean-v9.tex'
```

The pipeline performs these steps:

1. copy the privately supplied manuscript to the ignored `source_snapshot/`
   working directory;
2. compile it only under the ignored `output/manuscript/` directory;
3. extract source-bound inputs and current displayed numbering by stable LaTeX
   labels;
4. execute all Mathematica modules;
5. regenerate the result fragments and English verification manual;
6. run delivery-integrity and repository manuscript-exclusion checks.

Ordinary prose edits, line-number changes, and automatic theorem renumbering do
not require manual edits to the code or documentation. For mathematical
changes:

- edit the matching object in `config/verification_manifest.json` for a changed
  printed approximation;
- edit the matching module in `checks/` for a changed formula;
- add one manifest entry and one focused check block for a new computable
  component;
- add a Section 4 coverage entry when the new component is a Mathematica-
  checkable calculation in that section.

The manual imports all displayed manuscript references and result tables from
`generated/`. Do not edit those generated fragments by hand.

Before every push, run the repository-level policy check:

```powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '..\tools\check_no_manuscripts.py' --root '..'
```

The same check runs automatically on GitHub. It rejects unapproved `.tex` or
`.pdf` files, all manuscript working directories, disguised PDF/complete-TeX
documents, and opaque archives.
