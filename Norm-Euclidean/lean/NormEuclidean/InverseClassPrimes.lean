import NormEuclidean.ClassNumberReduction

/-!
# The isolated inverse-class prime-existence input

This is the precise remaining number-field theorem used by the rank-at-least-
three route. It is an explicit proposition parameter, not an axiom or a theorem
asserting its truth. It supplies only prime ideals and principal products,
never lattice vectors, norm descent, content, or a class-number conclusion.
-/

namespace NormEuclidean

variable (K : Type*) [Field K] [NumberField K]

/-- A prime in each inverse ideal class, avoiding a prescribed nonzero
principal ideal and the original ideal. The manuscript obtains this input
from the ordinary Hilbert class field and Chebotarev. -/
def HasInverseClassPrimesAway : Prop :=
  ∀ i : Ideal (integerSubring K), i ≠ ⊥ →
    ∀ d : integerSubring K, d ≠ 0 →
      ∃ p : Ideal (integerSubring K), p.IsMaximal ∧ p ≠ ⊥ ∧ IsCoprime i p ∧ d ∉ p ∧
        ∃ a : integerSubring K, a ≠ 0 ∧ i * p = Ideal.span {a}

/-- Apply prime avoidance to `2t`. This is a proved consequence of the
explicit prime-existence input, not a replacement for that input. -/
theorem inverse_class_prime_avoiding_two_and_denominator
    (hprime : HasInverseClassPrimesAway K)
    (i : Ideal (integerSubring K)) (hi : i ≠ ⊥)
    (t : integerSubring K) (ht : t ≠ 0) :
    ∃ p : Ideal (integerSubring K), p.IsMaximal ∧ p ≠ ⊥ ∧ IsCoprime i p ∧
      (2 : integerSubring K) ∉ p ∧ t ∉ p ∧
        ∃ a : integerSubring K, a ≠ 0 ∧ i * p = Ideal.span {a} := by
  obtain ⟨p, hp, hp0, hcop, havoid, a, ha, hgen⟩ :=
    hprime i hi (2 * t) (mul_ne_zero (by norm_num) ht)
  refine ⟨p, hp, hp0, hcop, ?_, ?_, a, ha, hgen⟩
  · intro htwo
    exact havoid (p.mul_mem_right t htwo)
  · intro htmem
    exact havoid (p.mul_mem_left 2 htmem)

end NormEuclidean
