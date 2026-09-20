# Reproducing the v15 release

## Fixed inputs

- Author source SHA-256: 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
- Lean toolchain: v4.32.1, recorded in lean/lean-toolchain.
- mathlib revision: 520045ab14e26149ee970e2e617ca04b09bde5d6, pinned in lean/lake-manifest.json.
- Public extracted input: inputs/manuscript_inputs_v15.json. The manuscript itself is kept private.

## Public computational rerun

From Trace-Euclidean:

~~~powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\verify_public_v15.py'
& 'C:\Program Files\Wolfram Research\WolframScript\wolframscript.exe' -file '.\checks\v15_classification.wls'
~~~

Expected: 1156 Python PASS, 115 Wolfram PASS, zero failures. The v15 summaries
are under results/python_v15_summary.json and
results/v15-mathematica-transcript.txt. Executable paths may be adapted.

## Lean rerun

From Trace-Euclidean/lean:

~~~powershell
& 'C:\Users\hzlde\.elan\bin\lake.exe' exe cache get
& 'C:\Users\hzlde\.elan\bin\lake.exe' build
& 'C:\Users\hzlde\.elan\bin\lake.exe' env lean '.\TraceEuclideanTest\MainTheoremAudit.lean'
~~~

The first command is needed only on a fresh checkout. The build and audit
commands must exit successfully. Compare the axiom report with
lean/audit/main_theorem_axioms.txt; the audited v15 declarations should
list only propext, Classical.choice, and Quot.sound. On resource-limited
Windows systems, set LEAN_NUM_THREADS to 4.

## Private maintainer source check

The source-bound Python and Wolfram checks live outside this public
repository. The frozen manuscript and its working copy have the SHA-256 above.
Those runs produced 1165 Python PASS and 112 Wolfram PASS. This step verifies
that the public extracted inputs correspond to the author's v15 source.

Before every push, from the repository root run:

~~~powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\check_no_manuscripts.py' --root '.'
~~~

The v9 verification manual and 2165-check result set remain historical and
must not be treated as v15 checks.
