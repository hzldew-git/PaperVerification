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
- The concrete field classification retains square-free `m>1`, the actual
  ring of integers in both residue cases, strict trace-square cost, and both
  directions of the iff.
- Each of the eight finiteness endpoints retains the paper's fixed or varying
  rank and degree pattern and the restriction `t ≤ d`.

## Generalized but semantically thinner statements

`StrictEuclidean` and `IsometricForms` quantify over arbitrary types. This
makes their logical conclusions more general, but removes the field, module,
lattice, and integrality content needed by the paper. This syntactic
generality must not be reported as a stronger formalization of the paper.

`SquaredCoveringRadiusSpecOver` characterizes a least upper bound through an
upper approximation property and sharp failure below the proposed value. This
is order-theoretically sufficient for the classification, but an independent
reviewer must confirm that it is accepted as the manuscript's covering-radius
normalization.

## Conditionalized statements

- The p-norm conclusion assumes the pointwise power-mean inequality.
- The Hessian conclusion assumes the differentiated critical identities.
- Voronoi coefficient and norm formulas assume a nonzero Gram determinant.
- The generic coordinate-model classification assumes an integral-coordinate
  equivalence, but the public concrete classification constructs it.
- The generic `MainFinitenessFramework` theorem accepts an interface value,
  while the public `GlobalFiniteness` endpoints instantiate every field with
  proved declarations and accept no additional mathematical premise.

## Missing theorem strength

Proposition 6.1, Theorem 1.8, Theorem 1.2(i)-(iv), and Theorem 1.3(i)-(iv)
have complete concrete endpoints and are `PROVISIONAL_MATCH`. The finiteness
proof uses a direct fixed-field finite-code argument instead of formalizing
the manuscript's standalone bounded-volume Lemma 5.1. This alternate route
proves the same main conclusions without stronger endpoint assumptions.

Supporting results remain partial: the full power-mean corollary, the general
`Phi` construction, the complete analytic maximum proofs, and every separate
scale/norm/volume-ideal inequality are not all formalized as paper-shaped Lean
theorems. These are documented coverage limits rather than gaps in the
transitive proof of a core endpoint. The project therefore meets Grade B and
does not meet Grade A while semantic review cards remain unsigned.
