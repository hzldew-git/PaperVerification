import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Rat.Cast.Order

/-!
# The actual absolute field norm and its integral descent measure

The codomain of `fieldAbsNorm` is `ℚ`: no analytic embedding or positivity
of a quadratic form is required. The natural-valued measure is defined on
the entire field, but its agreement with the absolute norm is asserted
only for algebraic integers. It is not a Euclidean-function assumption.
-/

namespace NormEuclidean

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The ring of integers as a subring of the specified number field. -/
def integerSubring : Subring K := (integralClosure ℤ K).toSubring

omit [NumberField K] in
@[simp] theorem mem_integerSubring (a : K) :
    a ∈ integerSubring K ↔ IsIntegral ℤ a := Iff.rfl

instance integerSubring_isFractionRing : IsFractionRing (integerSubring K) K :=
  inferInstanceAs (IsFractionRing (𝓞 K) K)

instance integerSubring_isDedekindDomain : IsDedekindDomain (integerSubring K) :=
  inferInstanceAs (IsDedekindDomain (𝓞 K))

/-- Absolute field norm, with its natural rational-valued codomain. -/
noncomputable def fieldAbsNorm (a : K) : ℚ := |Algebra.norm ℚ a|

/-- A total natural-valued measure. For nonintegral arguments this is
the absolute numerator of the norm; those values are never used by descent. -/
noncomputable def integralNormMeasure (a : K) : ℕ := (Algebra.norm ℚ a).num.natAbs

@[simp] theorem fieldAbsNorm_zero : fieldAbsNorm K 0 = 0 := by
  simp [fieldAbsNorm]

@[simp] theorem fieldAbsNorm_one : fieldAbsNorm K 1 = 1 := by
  simp [fieldAbsNorm]

theorem fieldAbsNorm_mul (a b : K) :
    fieldAbsNorm K (a * b) = fieldAbsNorm K a * fieldAbsNorm K b := by
  simp only [fieldAbsNorm, map_mul, abs_mul]

@[simp] theorem fieldAbsNorm_neg (a : K) :
    fieldAbsNorm K (-a) = fieldAbsNorm K a := by
  have h : Algebra.norm ℚ (-1 : K) = (-1 : ℚ) ^ Module.finrank ℚ K := by
    simpa using (Algebra.norm_algebraMap (R := ℚ) (S := K) (-1 : ℚ))
  unfold fieldAbsNorm
  calc
    |Algebra.norm ℚ (-a)| =
        |Algebra.norm ℚ (-1 : K) * Algebra.norm ℚ a| := by
      rw [← map_mul, neg_one_mul]
    _ = |Algebra.norm ℚ a| := by rw [abs_mul, h, abs_pow]; simp

theorem fieldAbsNorm_nonneg (a : K) : 0 ≤ fieldAbsNorm K a := abs_nonneg _

theorem fieldAbsNorm_pos {a : K} (ha : a ≠ 0) : 0 < fieldAbsNorm K a :=
  abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr ha)

@[simp] theorem fieldAbsNorm_eq_zero_iff (a : K) : fieldAbsNorm K a = 0 ↔ a = 0 := by
  simp [fieldAbsNorm]

/-- The integer norm computes the natural measure of an algebraic integer. -/
theorem integralNormMeasure_coe (a : 𝓞 K) :
    integralNormMeasure K (a : K) = (Algebra.norm ℤ a).natAbs := by
  unfold integralNormMeasure
  rw [← Algebra.coe_norm_int a, Rat.num_intCast]

/-- Integrality turns the rational absolute field norm into an actual
natural number. This is the bridge used in the well-founded descent. -/
theorem integralNormMeasure_spec (a : K) (ha : a ∈ integerSubring K) :
    (integralNormMeasure K a : ℚ) = fieldAbsNorm K a := by
  let ai : 𝓞 K := ⟨a, ha⟩
  change (integralNormMeasure K (ai : K) : ℚ) = |Algebra.norm ℚ (ai : K)|
  rw [integralNormMeasure_coe, ← Algebra.coe_norm_int]
  simp only [Nat.cast_natAbs, Int.cast_abs]

theorem integralNormMeasure_pos {a : K} (ha : a ∈ integerSubring K) (ha0 : a ≠ 0) :
    0 < integralNormMeasure K a := by
  exact_mod_cast (show (0 : ℚ) < integralNormMeasure K a by
    rw [integralNormMeasure_spec K a ha]
    exact fieldAbsNorm_pos K ha0)

end NormEuclidean
