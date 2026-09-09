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

Status: `PARTIAL_FORMALIZATION`, Grade C. The project checks important proof
components and all identified Section 4 computations, but it does not contain
an end-to-end Lean theorem for Theorem 1.2, Theorem 1.3, Proposition 6.1, or
Theorem 1.8. Successful compilation is not a certificate that those complete
paper results are formally proved or semantically error-free.
