# Statement-strength report

## Preserved components

- The strict quantifier pattern `forall x, exists y` is preserved by
  `StrictEuclidean`.
- The radius bridge keeps the asymmetric strict/non-strict conclusions:
  `rhoSq<t` implies strict Euclideanity, while strict Euclideanity implies
  `rhoSq<=t`.
- The p-norm transfer preserves the witness dependence on `x`; it does not
  interchange the quantifiers.
- The corrected Lemma 4.3 component proves a strictly negative Hessian
  determinant, not merely a nonpositive one.
- The quadratic candidate lemmas retain the strict exclusion at `m=3` and
  distinguish the two congruence cases.

## Generalized but semantically thinner statements

`StrictEuclidean` and `IsometricForms` quantify over arbitrary types. This
makes their logical conclusions more general, but removes the field, module,
lattice, and integrality content needed by the paper. This syntactic
generality must not be reported as a stronger formalization of the paper.

`finite_positive_of_tendsto_atTop_atBot` is an exact abstract finiteness
principle for any sequence tending to minus infinity. It does not prove that
the manuscript's `g_s` or `g_n` sequences have that limit.

## Conditionalized statements

- The p-norm conclusion assumes the pointwise power-mean inequality.
- The Hessian conclusion assumes the differentiated critical identities.
- Voronoi coefficient and norm formulas assume a nonzero Gram determinant.
- Candidate classification assumes the two closed-radius formulas.
- Finiteness assembly assumes eventual negativity or finite fibers.

## Missing theorem strength

There is no Lean declaration with the full quantifiers and conclusion of
Theorem 1.2, Theorem 1.3, Proposition 6.1, or Theorem 1.8. In particular, the
formal source does not quantify over all totally real fields, all eligible
lattices, or the manuscript's equivalence classes of field-lattice pairs.

The correct project-level description is therefore `PARTIAL_FORMALIZATION`.
