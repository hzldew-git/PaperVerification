# Trace-Euclidean v15 trust boundary

Lean accepts the encoded proof terms under Lean 4.32.1 and pinned mathlib
revision 520045ab14e26149ee970e2e617ca04b09bde5d6. The audited v15
endpoints depend only on the standard logical axioms propext,
Classical.choice, and Quot.sound. A source scan found no sorry, sorryAx,
project axiom, native_decide, run_tac, unsafe, extern, or implemented_by in
the proof modules.

The global finite-class results explicitly accept
V15OdlyzkoTable4Input. It states the published unconditional Table 4 row
b=4 for every coded totally real field. The source gives
|D_F| > 36.347^d exp(-10.667). Lean proves the exponential comparison,
degree cutoff, rank-one integral-to-classic lemma, strict root bounds, and
finite assembly. The table is cited mathematical input, not a Lean axiom
proved by this package.

The public Python and Wolfram runs trust their kernels and the extracted
input file. The private maintainer run also checks the SHA-256 digest and
printed entries against the manuscript. Public reruns alone cannot
reconstruct a source file that is intentionally absent.

Theorem 1.7's Lean endpoint covers all nonzero fractional-ideal
presentations. The paper uses the standard representation of an abstract
rank-one lattice by such an ideal and a coefficient. The theorem
GlobalLatticePresentation.rankOne_ideal_bridge_at now exports this
presentation for the canonical rank-one global lattice model, including
positivity, integrality, and the strict trace condition at any real threshold.
Its degree specialization matches the manuscript. The theorem
v15AbstractToCanonicalAnyField adds an actual isometry from any positive-rank
abstract lattice over any totally real number field to a coded canonical
coordinate model, transporting the scalar field, full lattice, and quadratic
form while preserving strict trace Euclideanity and classic integrality;
v15AbstractRankOneIdealBridgeAnyField composes this with the ideal
representation. The field isomorphism identifies the integer rings and
preserves rational traces.
The theorem v15_proposition_six_one_full
exports the general reduced-binary covering
radius and determinant identity for actual fractional ideals and both
positive-integer scalar specializations on the full integer ring. Corollary
1.6 has a varying-field endpoint for finite p >= 1 and p = infinity. These
proofs have the same standard logical axiom dependencies as the existing
endpoints.
The main six-class theorem still uses its direct rational deep-hole argument
and constructive covers for the six survivors.

V15AnalyticTable evaluates the Gamma factor in `H(n,d)`, proves rational
enclosures for pi and the exponential correction, and kernel-checks all 476
rank-degree cells. Its two equivalence theorems prove that the analytic classic
and integral inequalities select exactly the 24 and 63 rows recorded in
V15AdmissibleTables. V15AnalyticTableBridge proves the downstream class-level
membership statements from two disclosed source premises:
V15SmallDegreeDiscriminantInput for degrees at most eleven and
V15OdlyzkoTable4Input for the remaining degrees. The cited field-discriminant
estimates themselves remain external; the analytic enclosure and finite-grid
classification are no longer outside Lean. Python and Wolfram provide
independent computational checks.

Compilation and PASS counts do not certify the complete manuscript.
The first-party [v15 semantic audit](docs/audit/v15/12_executive_summary.md)
records definition comparison, hidden assumptions, theorem scope,
reproducibility, and unsigned review cards. Grade B reflects substantial
formalization of the core claims; Grade A is not claimed.
