# Trust and proof scope

This project pins Lean 4.32.1 and mathlib in `lean/lean-toolchain` and
`lean/lake-manifest.json`. A successful `lake build` means Lean accepted the
encoded declarations against those dependencies. The dedicated axiom audits
show the transitive assumptions of selected endpoints.

The new real-product coordinate theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. Some finite numerical and generated
algebraic certificates use `native_decide`; those checks additionally trust
Lean's native compiler. Run

```powershell
cd lean
lake env lean TraceEuclideanTest/MainTheoremAudit.lean
lake env lean TraceEuclideanTest/NumericalAxiomAudit.lean
lake env lean TraceEuclideanTest/TraceProductCoordinatesAudit.lean
lake env lean TraceEuclideanTest/PoitouDegreeElevenAudit.lean
```

The global real covering maximum being attained at rational coordinates is
cited from Clark--Jagy. Lean proves rational-to-real nearest-value
compatibility and transfers such a maximizer to the original rational trace
space, but the general rational-attainment theorem itself is not yet proved
here.

The completeness of the archived Voight field enumeration is an external
literature input. For the degree-eleven bound, Lean proves the strict numerical
optimization producing 14.083, including the required infinite-sum estimate.
Its route through Poitou's specialized explicit formula still takes that
formula as a premise. An alternative route takes the published
Odlyzko--Martinet degree-eleven estimate directly as a literature input.
The degree-eleven numerical upper bound and its bridge were separately
audited to use only the three standard logical axioms above.
The archived finite rows have extensive internal Lean and independent
computational checks, but those checks do not prove the enumeration is
complete.

The Python and Mathematica scripts check the public extracted numerical
input. The author's source-to-input comparison is maintained separately;
this repository does not redistribute the manuscript or its private
identifying metadata. The paper-to-Lean correspondence of several main
results still warrants independent mathematical review. See
`THEOREM_INDEX.md` for the claim-by-claim scope.
