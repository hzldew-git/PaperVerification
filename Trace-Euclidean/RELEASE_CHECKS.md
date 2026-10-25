# Release checks

The current synchronization refreshes reference locators and the computational
archive. Its new checks are listed first. Full Lean build and axiom-audit
evidence is retained only for the unchanged proof tree described below;
this synchronization is not a new full Lean build.

## Synchronization checks, 2026-10-25

- All 66 public reference locators were compared with the accompanying paper.
  Only the page of equation (1.2) changed, from 5 to 4; its number is unchanged.
- Every non-locator field in `inputs/verification_inputs.json` is unchanged
  from commit `c101031778afa02d7631fd96712ce0a75ef53898`. The complete file
  digest changes because the locator is part of that file.
- Public Python checks were rerun: **1,156 PASS, 0 FAIL**.
- Both Mathematica wrappers were rerun with Mathematica 15.0.0: 17 Section 4
  assertions, 952 rational grid decisions, 87 rounded upper bounds, 115
  classification assertions, and all 2,773 archived Voight rows passed.
- All 18 JSON/CSV result payloads agree with the preceding release, excluding
  run provenance. Archived files use the repository's LF line endings before
  their SHA-256 digests are recorded.
- The `.m` source changed only in its introductory documentation comment.
  Its executable calculations are unchanged; the new code digest is bound
  to the repeated runs.
- The computational-result, manuscript-exclusion and public-metadata checks
  passed. The computational-result check now also runs on every GitHub push
  and pull request.

The exact source-to-input comparison is retained in a private correspondence
record. No manuscript file or internal manuscript identifier is distributed.

## Retained full Lean build evidence

The proof source at commit `72bfc64f98b11adbc0a625a95076e63c98219e79` was checked
in a fresh working tree and reproduced from a separate checkout. Both started
without project build artifacts, used the pinned dependencies and the official
mathlib dependency cache, and completed the full `lake build`.
The current `lean/` tree has the identical Git tree identifier
`55a8e66877921be32969f68e6dfc7a65a71b3bde`, including its toolchain and dependency
manifest. No Lean or mathlib upgrade was made.

- Lean 4.32.1, with the exact dependency revisions in `lean/lake-manifest.json`.
- Generated Voight certificates reproduce the committed source.
- The full Lean build and all four documented axiom audits: **PASS in both checkouts**.

## Axiom audit

The counts below are reports, not a count of distinct theorems across files.
Every reported axiom is either `propext`, `Classical.choice`, `Quot.sound`, or
the explicitly disclosed native computation axiom. The product-coordinate
and Poitou audit files permit only the three standard logical axioms.

In the pinned Lean toolchain, `native_decide` records individual computation
axioms with names ending in `._native.native_decide.ax_...`. These are counted
as native computation dependencies. Each reported generated axiom was checked
to be a closed Boolean decision equality and traced to a `native_decide`
invocation in the unchanged proof sources. This provenance check identifies
the disclosed compiler dependency; it does not remove that trust assumption.

| Audit file | Reports | Reports using native computation |
| --- | ---: | ---: |
| `TraceProductCoordinatesAudit` | 12 | 0 |
| `PoitouDegreeElevenAudit` | 7 | 0 |
| `MainTheoremAudit` | 591 | 0 |
| `NumericalAxiomAudit` | 72 | 23 |

The audit does not discharge explicit theorem hypotheses. In particular,
Voight enumeration completeness remains a literature input, as documented
in `TRUST.md` and `THEOREM_INDEX.md`. This release does not claim that every
statement of the accompanying paper has been independently formalized.

## Reproduction

Use the commands and troubleshooting steps in `README.md`. The full local
build is broader than the GitHub-hosted checks, which build and audit the
product-coordinate and closed Poitou endpoints and run the public source,
certificate, and Python checks. A fixed release tag identifies the files
that should be used together.

## Computational supplement

The computational supplement provides the reusable Mathematica source
`TraceEuclideanVerification.m` and 18 archived JSON/CSV result files under
`mathematica/`. The result manifest records SHA-256 digests of the code,
public inputs, and result files.

The archived Mathematica runs include 17 Section 4 assertions, 952 rational
grid decisions, 87 rounded upper bounds, 115 classification assertions,
and checks of all 2,773 archived Voight rows. These finite checks retain the
mathematical-input and computational-trust scope in `TRUST.md`.

The result checker verifies the code and input digests, every archived
result digest, and recorded outcomes. The public Python and publication
checks were rerun for the supplement.

The complete Lean source tree and pinned dependencies are identical to those
at the audited proof-source commit above. The mathematical input values are
unchanged; reference locator metadata and the complete input-file digest have
been refreshed as described above. The two full-build and four-audit results
are carried forward for that unchanged proof tree. The repeated computational
runs have their own current provenance and checks described in
`mathematica/README.md`.
