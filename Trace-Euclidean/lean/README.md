# Lean project

This directory contains the formalization and its imported certificate
libraries. Run `lake exe cache get` followed by `lake build` from here. The
toolchain and mathlib revision are pinned by `lean-toolchain` and
`lake-manifest.json`.

The library entry points are `TraceEuclidean.lean` and
`TraceEuclideanTest.lean`. The latter imports focused axiom audits. To inspect
the public theorem signatures and the numerical trust boundary, run:

```powershell
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
lake env lean TraceEuclideanTest/NumericalAxiomAudit.lean
```

The real-product coordinate proposition is in
`TraceEuclidean/TraceProductCoordinates.lean`; its axiom audit is in
`TraceEuclideanTest/TraceProductCoordinatesAudit.lean`. The generated
maximal-order and finite numerical certificates are required for the full
build. Their source files are part of this checkout.

Third-party code and license notices are recorded in `DedekindZeta/README.md`,
`LeanCert/VENDORED.md`, `IdealArithmetic/README.md`, and
`THIRD_PARTY_LICENSES/`.
