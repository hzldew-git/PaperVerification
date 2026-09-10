# Audit scope

## Target

This audit covers the author manuscript version identified as
`Trace-Euclidean-v9`, SHA-256
`a2f522d077c600e0dc747dcaa8b06ba4e31ecd0b49b83dae468c9b61915a0e99`,
and the Lean source under `lean/TraceEuclidean/`.

The manuscript was read from the private author workspace. It is intentionally
excluded from this public repository. The public extracted inputs retain stable
labels, displayed formulas, table values, and the source hash needed to bind the
computational evidence to that version.

## Method

The paper inventory in `01_paper_theorem_inventory.md` records definitions,
hypotheses, quantifiers, and conclusions before assigning Lean matches. The
formal inventory in `02_formal_declaration_inventory.md` records elaborated
Lean declarations by module. The comparison files then examine:

- definition and notation alignment;
- theorem hypotheses and quantifier order;
- strict versus non-strict boundary conditions;
- conclusion strength and classification scope;
- external inputs and hidden assumptions;
- trust, axiom, and reproducibility boundaries.

## Status vocabulary

- `PROVISIONAL_MATCH`: the reviewed statement appears semantically aligned,
  but independent author and Lean-expert sign-off is absent.
- `FORMALIZATION_WEAKER`: the formal theorem has a stronger assumption or a
  narrower object domain than the paper theorem.
- `FORMALIZED_COMPONENT`: Lean proves a specifically identified component.
- `PARTIAL_FORMALIZATION`: Lean covers some obligations but not the complete
  paper result.
- `NOT_FORMALIZED`: no Lean declaration is claimed for the result.
- `COMPUTATION_VERIFIED`: Mathematica checks the encoded computation.
- `EXTERNAL_INPUT`: a cited or mathematical input is not reproved here.

## Audit boundary

This is a first-party machine-assisted audit, not independent peer review.
Compilation proves acceptance of the encoded Lean statements. It does not prove
that every paper statement was encoded, that cited theorems are correct, or
that the complete paper is free of mathematical error.

The audit applies the same public-endpoint rule used by the author's BongTheory
work: a main endpoint is not treated as unconditional while it accepts a
project-specific structure containing proof obligations. The current eight
finiteness endpoints pass this gate: `MainFinitenessFramework` is instantiated
internally by proved declarations, and no framework value appears in a public
endpoint signature.
