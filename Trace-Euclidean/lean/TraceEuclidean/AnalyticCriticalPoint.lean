import Mathlib

/-!
Kernel-checked algebra for the repaired critical-point argument in the proof
of the global maximum of the analytic function `g`.
-/

namespace TraceEuclidean

/-- The numerator controlling the sign of the derivative of `f`. -/
theorem stationaryPolynomial_pos {b y : ℝ} (hb : 0 < b) (hy : 1 ≤ y) :
    0 < y ^ 2 + (2 * b - 1) * y + b ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hyy : 0 ≤ y * (y - 1) :=
    mul_nonneg (le_of_lt hy0) (sub_nonneg.mpr hy)
  have hby : 0 < 2 * b * y := mul_pos (mul_pos (by norm_num) hb) hy0
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  nlinarith

theorem stationaryDerivative_identity {b y : ℝ} (hyb : y + b ≠ 0) :
    y / (y + b) ^ 2 - 1 =
      -(y ^ 2 + (2 * b - 1) * y + b ^ 2) / (y + b) ^ 2 := by
  field_simp [hyb]
  ring

/-- The derivative `y/(y+b)^2 - 1` is strictly negative on the paper's domain. -/
theorem stationaryDerivative_neg {b y : ℝ} (hb : 0 < b) (hy : 1 ≤ y) :
    y / (y + b) ^ 2 - 1 < 0 := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hyb : 0 < y + b := add_pos hy0 hb
  rw [stationaryDerivative_identity (ne_of_gt hyb)]
  exact div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (stationaryPolynomial_pos hb hy)) (sq_pos_of_pos hyb)

/-- The two differentiated critical-point identities imply the Hessian identity. -/
theorem criticalPoint_hessian_identity {z gxx gxy gyy fprime : ℝ}
    (hxx : gxx = z * gxy) (hfp : fprime = gxy - z * gyy) :
    gxx * gyy - gxy ^ 2 = -gxy * fprime := by
  rw [hxx, hfp]
  ring

/-- Every critical point satisfying the repaired identities is a saddle point. -/
theorem criticalPoint_hessian_negative {z gxx gxy gyy fprime : ℝ}
    (hz : 0 < z) (hgxx : gxx < 0)
    (hxx : gxx = z * gxy) (hfp : fprime = gxy - z * gyy)
    (hfneg : fprime < 0) :
    gxx * gyy - gxy ^ 2 < 0 := by
  have hzgxy : z * gxy < 0 := hxx ▸ hgxx
  have hgxy : gxy < 0 := by
    rcases mul_neg_iff.mp hzgxy with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (le_of_lt hz)) h.1)
  rw [criticalPoint_hessian_identity hxx hfp]
  exact mul_neg_of_pos_of_neg (neg_pos.mpr hgxy) hfneg

end TraceEuclidean
