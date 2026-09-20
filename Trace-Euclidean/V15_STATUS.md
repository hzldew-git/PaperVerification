# Trace-Euclidean v15 verification work in progress

Frozen private manuscript SHA-256:
`83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5`.
The manuscript is intentionally absent from this public package.

This branch contains new v15 extracted inputs, independent Python and Wolfram
checks, and Lean modules for the reduced Gram sieve and variable-degree
finiteness assembly. The existing `README.md`, `THEOREM_INDEX.md`, `TRUST.md`,
and v9 results still describe the prior v9 release. They are not v15 claims.

## Verified components

- Public extracted-input Python rerun: 1,156 PASS, 0 FAIL.
- Public Wolfram rerun: 115 PASS, 0 FAIL.
- Lean `lake build`: successful on Lean 4.32.1 and the pinned mathlib revision.
- Lean proves the exact 22 Gram rows, the nine discriminant/parity rows, and
  the six rows left after the first trace/norm equation.
- Lean proves `rank ≤ 34` for the formal integral variable-degree class.
- Lean assembles global finiteness from the paper's `degree ≤ 14` bound, and
  derives that bound under explicit Odlyzko and rank-one classic-integrality
  inputs. Those inputs are not hidden axioms.
- Lean checks the six rational radius expressions. A separate proof is needed
  to identify them with the full covering radii of the relevant lattices.

## Remaining Grade B obligations

1. Connect the cited unconditional Odlyzko discriminant row to the formal
   coded fields without a theorem-level degree-bound premise.
2. Prove rank-one integral implies classic integral for arbitrary full
   projective ideal lattices, and derive the exact strict root-discriminant
   bounds of Theorems 1.2 and 1.3.
3. Bridge every rank-one fractional-ideal lattice to the reduced Gram and
   trace/norm/index conditions, prove the full binary covering formula,
   construct the six representatives, prove freeness and pairwise distinction.
4. Re-audit the inherited real-quadratic field endpoint against v15, refresh
   every v9 release document and result index, then run a clean release build.

Current v15 assessment: **Grade C, partial formalization**. The v9 Grade B
package must not be relabeled or replaced with this branch yet.

## Reproduce the new checks

From this directory:

```powershell
& 'D:\AI-Workspace\Environments\Python\math-research\Scripts\python.exe' '.\tools\verify_public_v15.py'
& 'C:\Program Files\Wolfram Research\WolframScript\wolframscript.exe' -file '.\checks\v15_classification.wls'
Set-Location '.\lean'
& 'C:\Users\hzlde\.elan\bin\lake.exe' build
```

The public checks trust the extracted input file; the source-bound extraction
and source SHA verification are performed in the private work area.
