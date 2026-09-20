# Author and formalization review cards

## Theorem 1.2: classic integral finiteness

Paper: finite isometry classes over all totally real fields and positive ranks, with strict n Delta_F^(1/d) < 2 pi e.

Formal: v15_classic_root_discriminant_lt and v15_classic_finite_of_odlyzko_table4. The finite theorem accepts the exact published Table 4 inequality as a cited external premise.

Status: PROVISIONAL_MATCH. AUTHOR_CONFIRMATION_REQUIRED for the cross-field isometry convention. FORMALIZATION_EXPERT_CONFIRMATION_REQUIRED for the quotient and analytic dependency chain.

## Theorem 1.3: integral finiteness

Paper: same varying field/rank scope and strict n Delta_F^(1/d) < 4 pi e.

Formal: v15_integral_root_discriminant_lt, v15_integral_rank_le_34, v15_rank_one_classic_input, and v15_integral_finite_of_odlyzko_table4_source.

Status: PROVISIONAL_MATCH. AUTHOR_CONFIRMATION_REQUIRED for volume-ideal and classic-integrality normalization. FORMALIZATION_EXPERT_CONFIRMATION_REQUIRED for the rank-one and scale-two bridges.

## Theorem 1.7: six rank-one classes

Paper: every positive integral rank-one lattice over a real quadratic field is trace Euclidean iff isometric to one of six free forms; exactly six classes.

Formal: v15_rank_one_real_quadratic_classification_totally_positive covers every nonzero fractional ideal; necessity proves principality, sufficiency transfers constructive covers, representative validity and distinction are separate checked declarations.

Status: PROVISIONAL_MATCH. AUTHOR_CONFIRMATION_REQUIRED that the standard abstract-lattice presentation as (I, alpha x^2) and the reduced-basis convention match the intended objects. FORMALIZATION_EXPERT_CONFIRMATION_REQUIRED for the ideal quotient/index and isometry-extension arguments.

## Corollary 1.9: trace Euclidean fields

Paper: Q(sqrt(m)) with square-free m > 1 is trace Euclidean iff m belongs to {2,5,13}.

Formal: realQuadratic_two_trace_euclidean_iff and the field-square bridge. The v15 manuscript still uses the same square form and strict threshold 2.

Status: PROVISIONAL_MATCH. AUTHOR_CONFIRMATION_REQUIRED for the field-model identification; independent Lean review remains unsigned.

## Corollary 1.6: p-norm finiteness

Paper: for each fixed p in [1, infinity], including house Euclideanity, positive integral lattices have finitely many isometry classes while the totally real field and positive rank vary.

Formal: V15PNormExponent covers every finite real p >= 1 and infinity. GlobalLatticePresentation.v15_pnorm_implies_trace proves the strict witness transfer from the normalized embedding mean to trace divided by degree. v15_pnorm_finite_of_odlyzko_table4 gives finite classes under the same disclosed Table 4 input as Theorem 1.3.

Status: PROVISIONAL_MATCH. AUTHOR_CONFIRMATION_REQUIRED for the embedding mean and cross-field isometry convention. FORMALIZATION_EXPERT_CONFIRMATION_REQUIRED for the mean inequality and quotient-class endpoint.

## Proposition 6.1: reduced radius and integer-scalar formulas

Paper: every qualifying rank-one fractional ideal has a reduced trace Gram basis, the determinant identity, and the exact squared radius; the full integer ring has two explicit formulas for every positive integer scalar.

Formal: v15_proposition_six_one_full combines v15_proposition_six_one_ideal with v15_proposition_six_one_scalar_cases. GlobalLatticePresentation.rankOne_ideal_bridge_degree supplies the canonical abstract rank-one presentation at the manuscript threshold.

Status: PROVISIONAL_MATCH. AUTHOR_CONFIRMATION_REQUIRED for the abstract-space and field-model identifications. FORMALIZATION_EXPERT_CONFIRMATION_REQUIRED for the ideal basis, integer-ring coordinate model, and sharp-radius transfer.
