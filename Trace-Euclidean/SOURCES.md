# Identified sources and external inputs

## Author version

The target is the privately held author file Trace-Euclidean-v15.tex with
SHA-256 83a236e93648ce0802f8a0d3022de63710d089f3a4f7e61214a4c855459597b5.
Public inputs/manuscript_inputs_v15.json records its extracted mathematical
data and labels without publishing the manuscript.

## Formal platform

Lean v4.32.1 and pinned mathlib revision
520045ab14e26149ee970e2e617ca04b09bde5d6.
Library theorems on number fields, fractional ideals, discriminants,
projective modules, Hermite finiteness, Haar covolume, and real analysis are
trusted as pinned mathlib dependencies.

## Odlyzko discriminant input

[Odlyzko, unconditional Table 4](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.table4)
lists row b=4.000 with A=36.347 and E=10.667.
His [description of the tables](https://www-users.cse.umn.edu/~odlyzko/unpublished/discr.bound.tables.txt)
states that Table 4 is unconditional, gives the general discriminant
inequality and explains the direction of rounding. The Table 4 header
directly states the bound used here. For a totally real field, its consequence
is |D_F| > 36.347^d exp(-10.667). The formal proposition
V15OdlyzkoTable4Input records exactly this consequence for coded fields.
The mathematical source is external; the numerical conversion and
downstream v15 finiteness proof are in Lean.

Voight's totally real field enumeration supplies the separate small-degree
discriminant estimates used by the paper's tables. The formal proposition
V15SmallDegreeDiscriminantInput records the required statement for degrees at
most eleven. Together with V15OdlyzkoTable4Input it yields
V15SectionFourDiscriminantInput. These cited estimates remain external; Lean
proves the exact analytic reduction and every subsequent finite-grid result.

## Unformalized standalone material

The generic binary-radius formula, Proposition 6.1's two integer-scalar
specializations, the p-norm finiteness corollary, the Section 4 analytic grid,
and its finite-table maxima now have standalone Lean endpoints. The complete
periodic-minimum development, all separate ideal upper bounds, and historical
or novelty assertions are not claimed as standalone Lean results. See the
[coverage report](docs/audit/v15/09_coverage_report.md).
