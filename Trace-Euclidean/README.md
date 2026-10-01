# Trace-Euclidean verification

This directory contains Lean proofs and independent Python and Mathematica
checks for selected claims of the accompanying paper. The manuscript itself
is not distributed here. The extracted numerical inputs are public; the
source-to-input comparison is maintained in a separate private audit.

## What is checked

- Lean proves the stated trace-lattice coordinate construction in the product
  of real embedding spaces, including the integral coordinate form and its
  nearest-lattice formula.
- Lean formalizes substantial parts of the finiteness, rank-one
  classification, and discriminant-bound arguments. See `THEOREM_INDEX.md`
  for the exact theorem names and remaining source inputs.
- The Python checker verifies the extracted numerical tables and finite
  rank-one candidate calculations. The Mathematica checker independently
  verifies the exact classification and Voronoi calculations.

Successful compilation certifies the encoded Lean statements relative to
their dependencies. It does not by itself certify that every sentence of the
paper has been formalized or that the extracted inputs match a private
manuscript copy.

## Reproduce

From this directory, run:

```powershell
python -m pip install -r requirements.txt
python tools/verify_public.py
python tools/check_no_manuscripts.py
python tools/check_public_metadata.py
wolframscript -file checks/classification.wls
```

The expected summaries are 1,156 Python PASS and 115 Mathematica PASS, with
zero failures. The two publication checks report PASS, confirming that the
candidate contains no manuscript documents, internal manuscript labels, or
local absolute paths. The numerical scripts write their summaries to `results/`.

For Lean, use the pinned toolchain and dependencies in `lean/`:

```powershell
cd lean
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
lake env lean TraceEuclideanTest/NumericalAxiomAudit.lean
lake env lean TraceEuclideanTest/TraceProductCoordinatesAudit.lean
lake env lean TraceEuclideanTest/PoitouDegreeElevenAudit.lean
```

`lake build` checks the full project. The audit commands print theorem
signatures and transitive axiom dependencies. The generated finite
certificates include `native_decide`, so those proofs additionally trust
Lean's native compiler; see `TRUST.md`.

The GitHub-hosted workflow builds the product-coordinate and closed
degree-eleven certificate modules and audits their 16 listed declarations.
It also checks the source, generated data, and public Python certificates.
This bounded workflow fits standard hosted runners; it is not a substitute
for the full `lake build` and the main and numerical axiom audits above.
A full clean build needs approximately 40 GB for `.lake`; allow at least
45 GB of free disk space and use the memory setting below if needed.

## Troubleshooting

- If `lake` selects the wrong Lean version, use the repository's
  `lean/lean-toolchain` through Elan and rerun from `lean/`.
- If dependency download or cache retrieval fails, check network access and
  rerun the same command. Keep `lean/lake-manifest.json` unchanged.
- If a certificate import is missing, ensure the checkout includes the full
  `lean/TraceEuclidean/` directory; avoid copying individual `.lean` files.
- If the full Lean build exhausts memory, set `LEAN_NUM_THREADS=1` and rerun
  `lake build` from `lean/`. In PowerShell use `$env:LEAN_NUM_THREADS='1'`;
  in a Unix shell use `export LEAN_NUM_THREADS=1`.
- If `wolframscript` is unavailable, install or license Wolfram Engine or
  Mathematica; the Python and Lean checks can still run independently.

The code and extracted data are intended to be used together at one fixed
repository commit. Results from mixed commits are not a verified run.
