# Trust boundary

This package separates four claims.

1. **Lean kernel acceptance.** Lean accepts the encoded declarations and proof
   terms.
2. **Computational verification.** Wolfram Language checks the encoded exact
   identities, rational certificates, finite enumerations, and displayed
   approximations.
3. **Technical reproducibility.** A checkout can rebuild the pinned Lean
   project and rerun the public computational package.
4. **Semantic fidelity.** The encodings have the same definitions, hypotheses,
   quantifiers, boundary conditions, and conclusions as the identified paper.

The first three have executable evidence. The fourth requires mathematical and
formalization review and is documented under `docs/audit/`.

## Lean proof boundary

The Lean project pins Lean `v4.32.1` and mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`. A complete `lake build` succeeds.
The public endpoint audit reports only `propext`, `Classical.choice`, and
`Quot.sound`, which are standard Lean/mathlib logical dependencies.

The formal source contains no `sorry`, `sorryAx`, project `axiom`,
`native_decide`, `run_tac`, `unsafe`, `extern`, or `implemented_by`.
`VoronoiAlgebra.lean` uses a `noncomputable section` because real-number
division is not executable data; every theorem still has a proof term and this
does not add an axiom.

## Computational boundary

The public computational rerun trusts the Wolfram kernel, the small Python
reporting scripts, and the extracted input file. Exact symbolic equalities and
rational interval certificates are stronger evidence than decimal agreement;
finite high-precision gamma diagnostics remain diagnostics. Cited analytic,
geometry-of-numbers, algebraic-number-theory, and quadratic-lattice theorems
are external inputs unless a ledger entry says otherwise.

## Semantic status

Status: `PARTIAL_FORMALIZATION`, Grade C.

Theorem 1.8 now has a concrete end-to-end Lean endpoint for
`QuadraticAlgebra ℚ m 0`, and Proposition 6.1 has exact full-plane
covering-radius specifications in both congruence cases. These are
`PROVISIONAL_MATCH` pending independent semantic review.

Theorems 1.2 and 1.3 have all eight final finiteness clauses with their
paper-level rank, degree, and `t ≤ d` quantifiers. Their proofs use Lean-proved
analytic tails, Hermite finiteness, and ideal enumeration, but the endpoint
signatures still take `MainFinitenessFramework`. That structure assumes the
geometric discriminant/volume estimates and the fixed-field fixed-volume
lattice finiteness used in the manuscript. Since it has not been instantiated
for the actual field-lattice equivalence classes, these two core theorem groups
remain `FORMALIZATION_WEAKER`. This disclosed gap prevents Grade B under the
same endpoint standard used for BongTheory.
