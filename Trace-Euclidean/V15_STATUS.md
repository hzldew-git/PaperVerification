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
  the six rows left after the first trace/norm equation. It also proves first
  ideal index one for every surviving row except `m=3`, and enumerates the
  three trace/norm/index solutions in that exceptional row.
- Lean proves `rank ≤ 34` for the formal integral variable-degree class.
- Lean proves the strict root-discriminant inequalities of Theorems 1.2 and
  1.3. It also proves that every integral rank-one presentation is classic
  integral, including nonfree fractional-ideal lattices.
- Lean derives `degree ≤ 14` and both global finiteness conclusions from the
  published form of Odlyzko Table 4, row `b=4`. The table's discriminant
  inequality remains an explicit cited external input; the numerical
  conversion and all later deductions are proved without project axioms.
- Lean proves the two-vector exclusion in the exceptional `m=3` row under the
  paper's trace/norm and coordinate hypotheses.
- Lean checks the six rational radius expressions. A separate proof is needed
  to identify them with the full covering radii of the relevant lattices.

## Remaining Grade B obligations

1. Record the cited Odlyzko Table 4 theorem as an accepted external result
   for the formal coded fields, with its source and scope audited. The exact
   table inequality is still a theorem parameter in the public Lean API.
2. Bridge every rank-one fractional-ideal lattice to the reduced Gram and
   trace/norm/index conditions, prove the full binary covering formula,
   construct the six representatives, prove freeness and pairwise distinction.
3. Re-audit the inherited real-quadratic field endpoint against v15, refresh
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
