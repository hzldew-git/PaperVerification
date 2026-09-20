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

## Card C: pseudobasis determinant and scaling

- [ ] Mathematical author confirms that
  `span(det B_z) * (∏ a_i)^2` is the manuscript's volume-ideal
  normalization.
- [ ] Lean reviewer confirms the pseudobasis construction, determinant
  change-of-basis formula, ideal integrality, nonvanishing, and exact
  `2^(nd)` scale factor.
- Current status: `PROVISIONAL_MATCH` for the determinant/covolume chain.

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
- [ ] Domain reviewer validates the alternative direct fixed-field
  finite-code argument and its equality-to-isometry reconstruction.
- [ ] Lean reviewer confirms the actual quotient, nonfree pseudobasis route,
  Hermite assembly, analytic tails, and absence of extra endpoint premises.
- Current status: `PROVISIONAL_MATCH`.
