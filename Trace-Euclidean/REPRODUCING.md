# Reproducing the verification

## Frozen inputs

- Manuscript identity: SHA-256
  `a2f522d077c600e0dc747dcaa8b06ba4e31ecd0b49b83dae468c9b61915a0e99`.
- Lean toolchain: `v4.32.1`, pinned by `lean/lean-toolchain`.
- mathlib: revision `520045ab14e26149ee970e2e617ca04b09bde5d6`, pinned
  with all transitive packages by `lean/lake-manifest.json`.
- The manuscript TeX and PDF are outside the repository and are not needed for
  the public reruns.

## Lean clean-checkout protocol

From `Trace-Euclidean/lean`:

```text
lake exe cache get
lake build
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
```

Success requires zero exit codes. The last command must print 13 endpoint
signatures, each with exactly `propext`, `Classical.choice`, and
`Quot.sound`. The initial verified Windows run used Lean 4.32.1 and Lake 5.0.0
and completed 8,665 Lake jobs.

## Public computational protocol

From `Trace-Euclidean`:

```powershell
wolframscript -file .\run_verification.wls
python .\tools\build_report.py
python .\tools\check_delivery.py
```

The expected computational result is `2165 PASS / 0 WARN / 0 FAIL`. The public
run validates the frozen extracted inputs and package correspondence. A
maintainer can privately rebind those inputs to a revised manuscript with
`build_all.ps1 -ManuscriptPath <outside-repository-path>`.

From the repository root, run the publication gate before every push:

```text
python tools/check_no_manuscripts.py --root .
```

GitHub Actions repeats the Lean build, forbidden-construct scan, endpoint axiom
audit, and manuscript-exclusion check on a fresh Ubuntu runner.
