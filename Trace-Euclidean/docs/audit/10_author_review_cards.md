# Author and independent-review cards

Each card remains unsigned. A check mark should be added only by the named
reviewer after comparing the identified manuscript version with the formal
signature and proof scope.

## Card A: Euclidean definitions

- [ ] Mathematical author confirms the cost normalization and strict inequality.
- [ ] Lean reviewer confirms `traceCost`, full-lattice semantics, the
  associated-bilinear-form normalization, and quantifier order.
- Current status: `PROVISIONAL_MATCH`.

## Card B: p-norm corollary

- [ ] Mathematical author confirms the uniform use of `t=d` as the field varies.
- [ ] Lean reviewer confirms that the formal theorem covers only witness
  transfer after pointwise domination is supplied.
- Current status: `FORMALIZED_COMPONENT`.

## Card C: scaling step in Lemma 5.1

- [ ] Mathematical author confirms scale, norm, and volume-ideal identities.
- [ ] Lean reviewer confirms the factor-two cancellation and that the scaled
  volume ideal in `MainFinitenessFramework` still requires a concrete
  instantiation.
- Current status: `FORMALIZATION_WEAKER`.

## Card D: repaired Lemma 4.3

- [ ] Mathematical author confirms the derivative identities and boundary
  decomposition.
- [ ] Lean reviewer confirms the stationary derivative and Hessian sign proof.
- [ ] Independent computational reviewer checks the rational boundary
  certificates and tail monotonicity.
- Current status: `PARTIAL_FORMALIZATION`.

## Card E: Proposition 6.1

- [ ] Mathematical author confirms that the order-theoretic upper-plus-sharp
  radius specification is equivalent to the stated covering radius.
- [ ] Lean reviewer confirms the full-plane rounding proof, deep-hole lower
  bound, and both formula normalizations.
- Current status: `PROVISIONAL_MATCH`.

## Card F: Theorem 1.8

- [ ] Mathematical author confirms that `QuadraticAlgebra ℚ m 0` and the two
  proved integral bases express the intended `Q(sqrt m)`.
- [ ] Lean reviewer confirms the concrete number-field instance, exhaustive
  ring-of-integers coordinates, trace-square bridge, necessity, `m=3`
  obstruction, and sufficiency.
- Current status: `PROVISIONAL_MATCH`.

## Card G: global finiteness

- [ ] Mathematical author confirms that the four classic and four integral
  endpoint quantifiers match Theorems 1.2 and 1.3.
- [ ] Domain reviewer validates the discriminant/volume bounds and O'Meara
  103:4 plus Remark 103:5 for the exact equivalence relation.
- [ ] Lean reviewer constructs the actual quotient of field-lattice pairs and
  an unconditional instance replacing `MainFinitenessFramework`.
- Current status: `FORMALIZATION_WEAKER`.
