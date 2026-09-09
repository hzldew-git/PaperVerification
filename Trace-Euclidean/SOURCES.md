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

## External mathematical inputs

The following source-dependent steps are not reproved end to end in Lean:

- compactness and Voronoi-cell facts used for covering radii;
- Euclidean ball-volume bounds and gamma-function inequalities;
- number-field discriminant finiteness;
- finiteness of quadratic spaces and lattice classes with bounded ideal data;
- integral bases of real quadratic fields and strict obtuse-superbase/Voronoi
  vector results;
- the cited classification of norm-Euclidean real quadratic fields.

Exact locators and bibliography entries remain in the author manuscript. The
semantic audit treats these as `EXTERNAL_INPUT`; neither successful Lean
compilation nor the Mathematica run independently validates the cited source
theorems.
