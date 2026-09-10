# Identified sources and external inputs

## Audited manuscript identity

The verification target is the local author version named
`Trace-Euclidean-v9`, SHA-256
`a2f522d077c600e0dc747dcaa8b06ba4e31ecd0b49b83dae468c9b61915a0e99`.
The repository records its extracted labels, formulas, table entries, and hash
in `inputs/manuscript_inputs.json`; it does not redistribute the manuscript.

## Formal platform

- Lean `v4.32.1`, pinned by `lean/lean-toolchain`.
- mathlib revision `520045ab14e26149ee970e2e617ca04b09bde5d6`, pinned by
  `lean/lake-manifest.json`.

## Library and external mathematical inputs

The Lean proofs rely on pinned mathlib results for Dedekind domains and
projective modules, fractional ideals and their norms, number-field trace and
discriminant theory, Hermite finiteness, Haar measure and lattice covolume, and
real Gamma-function analysis. These results are part of the disclosed trusted
library dependency rather than project axioms.

The global finiteness endpoints do not assume O'Meara's fixed-volume
classification: `DirectFixedFieldFiniteness` supplies an alternative finite
reduction-code proof. The real-quadratic endpoint also constructs both rings
of integers and proves a full-plane covering argument instead of assuming the
cited Voronoi classification.

The following manuscript material is not reproved end to end in Lean:

- the complete periodic-minimum function and compact-quotient development in
  Lemma 2.1;
- every separate scale-, norm-, and volume-ideal upper bound in Lemma 3.4;
- the complete global-maximum statements of Lemmas 4.1--4.9;
- the full power-mean definitions and Corollary 1.6;
- historical, bibliographic, and norm-Euclidean classification claims.

Exact locators and bibliography entries remain in the author manuscript.
Neither successful Lean compilation nor the Mathematica run independently
validates manuscript prose or cited-source claims outside the stated formal
dependency chain.
