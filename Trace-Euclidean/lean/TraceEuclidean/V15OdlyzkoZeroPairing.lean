import TraceEuclidean.V15OdlyzkoEntire
import TraceEuclidean.V15OdlyzkoPhiSymmetry

/-!
# Conjugate pairing of the Odlyzko zero transform

These identities make the zero term real and nonnegative when zeros are
paired with their complex conjugates. They also show that convergence of the
paired complex series is equivalent to convergence of its real contributions.
The existence, count, and distribution of Dedekind-zeta zeros remain separate.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

/-- The source transform commutes with complex conjugation. -/
theorem v15OdlyzkoPhi_conj (s : ℂ) :
    v15OdlyzkoPhi (conj s) = conj (v15OdlyzkoPhi s) := by
  unfold v15OdlyzkoPhi
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    map_sub, map_div₀, map_ofNat]
  simp

/-- The transform of a real spectral parameter is real. -/
theorem v15OdlyzkoPhi_im_eq_zero_of_im_eq_zero (s : ℂ) (hs : s.im = 0) :
    (v15OdlyzkoPhi s).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← v15OdlyzkoPhi_conj, Complex.conj_eq_iff_im.mpr hs]

/-- Reflection about the central line followed by conjugation has the same
effect on the transform as conjugation alone. -/
theorem v15OdlyzkoPhi_one_sub_conj (s : ℂ) :
    v15OdlyzkoPhi (1 - conj s) = conj (v15OdlyzkoPhi s) := by
  rw [v15OdlyzkoPhi_one_sub, v15OdlyzkoPhi_conj]

/-- One conjugate pair contributes exactly twice the real part. -/
theorem v15OdlyzkoPhi_conj_pair (s : ℂ) :
    v15OdlyzkoPhi s + v15OdlyzkoPhi (conj s) =
      ((2 * (v15OdlyzkoPhi s).re : ℝ) : ℂ) := by
  rw [v15OdlyzkoPhi_conj]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    ring
  · simp [Complex.add_im]

/-- A conjugate zero pair has nonnegative real contribution in the closed
critical strip. -/
theorem v15OdlyzkoPhi_conj_pair_nonneg (s : ℂ)
    (h₁ : 0 ≤ s.re) (h₂ : s.re ≤ 1) :
    0 ≤ (v15OdlyzkoPhi s + v15OdlyzkoPhi (conj s)).re := by
  rw [v15OdlyzkoPhi_conj_pair]
  exact mul_nonneg (by norm_num) (v15OdlyzkoPhi_re_nonneg_of_mem_closed_strip s h₁ h₂)

/-- Summability of conjugate-paired complex terms is equivalent to summability
of the real source contributions. -/
theorem v15OdlyzkoPhi_conj_pair_summable_iff {ι : Type*} (zeros : ι → ℂ) :
    Summable (fun i ↦ v15OdlyzkoPhi (zeros i) +
      v15OdlyzkoPhi (conj (zeros i))) ↔
      Summable (fun i ↦ (v15OdlyzkoPhi (zeros i)).re) := by
  simp_rw [v15OdlyzkoPhi_conj_pair]
  rw [Complex.summable_ofReal]
  exact summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)

/-- The sum of conjugate-paired terms equals twice the real zero sum. -/
def v15OdlyzkoZeroRealSum {ι : Type*} (zeros : ι → ℂ) : ℝ :=
  ∑' i, (v15OdlyzkoPhi (zeros i)).re

theorem v15OdlyzkoPhi_conj_pair_tsum {ι : Type*} (zeros : ι → ℂ)
    (h : Summable (fun i ↦ (v15OdlyzkoPhi (zeros i)).re)) :
    (∑' i : ι, (v15OdlyzkoPhi (zeros i) + v15OdlyzkoPhi (conj (zeros i)))) =
      ((2 * v15OdlyzkoZeroRealSum zeros : ℝ) : ℂ) := by
  unfold v15OdlyzkoZeroRealSum
  simp_rw [v15OdlyzkoPhi_conj_pair]
  rw [← Complex.ofReal_tsum, h.tsum_mul_left]

end
end TraceEuclidean
