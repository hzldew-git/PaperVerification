import TraceEuclidean.OdlyzkoEntire
import TraceEuclidean.OdlyzkoPhiSymmetry

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
theorem odlyzkoPhi_conj (s : ℂ) :
    odlyzkoPhi (conj s) = conj (odlyzkoPhi s) := by
  unfold odlyzkoPhi
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    map_sub, map_div₀, map_ofNat]
  simp

/-- The transform of a real spectral parameter is real. -/
theorem odlyzkoPhi_im_eq_zero_of_im_eq_zero (s : ℂ) (hs : s.im = 0) :
    (odlyzkoPhi s).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← odlyzkoPhi_conj, Complex.conj_eq_iff_im.mpr hs]

/-- Reflection about the central line followed by conjugation has the same
effect on the transform as conjugation alone. -/
theorem odlyzkoPhi_one_sub_conj (s : ℂ) :
    odlyzkoPhi (1 - conj s) = conj (odlyzkoPhi s) := by
  rw [odlyzkoPhi_one_sub, odlyzkoPhi_conj]

/-- One conjugate pair contributes exactly twice the real part. -/
theorem odlyzkoPhi_conj_pair (s : ℂ) :
    odlyzkoPhi s + odlyzkoPhi (conj s) =
      ((2 * (odlyzkoPhi s).re : ℝ) : ℂ) := by
  rw [odlyzkoPhi_conj]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    ring
  · simp [Complex.add_im]

/-- A conjugate zero pair has nonnegative real contribution in the closed
critical strip. -/
theorem odlyzkoPhi_conj_pair_nonneg (s : ℂ)
    (h₁ : 0 ≤ s.re) (h₂ : s.re ≤ 1) :
    0 ≤ (odlyzkoPhi s + odlyzkoPhi (conj s)).re := by
  rw [odlyzkoPhi_conj_pair]
  exact mul_nonneg (by norm_num) (odlyzkoPhi_re_nonneg_of_mem_closed_strip s h₁ h₂)

/-- Summability of conjugate-paired complex terms is equivalent to summability
of the real source contributions. -/
theorem odlyzkoPhi_conj_pair_summable_iff {ι : Type*} (zeros : ι → ℂ) :
    Summable (fun i ↦ odlyzkoPhi (zeros i) +
      odlyzkoPhi (conj (zeros i))) ↔
      Summable (fun i ↦ (odlyzkoPhi (zeros i)).re) := by
  simp_rw [odlyzkoPhi_conj_pair]
  rw [Complex.summable_ofReal]
  exact summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)

/-- The sum of conjugate-paired terms equals twice the real zero sum. -/
def odlyzkoZeroRealSum {ι : Type*} (zeros : ι → ℂ) : ℝ :=
  ∑' i, (odlyzkoPhi (zeros i)).re

theorem odlyzkoPhi_conj_pair_tsum {ι : Type*} (zeros : ι → ℂ)
    (h : Summable (fun i ↦ (odlyzkoPhi (zeros i)).re)) :
    (∑' i : ι, (odlyzkoPhi (zeros i) + odlyzkoPhi (conj (zeros i)))) =
      ((2 * odlyzkoZeroRealSum zeros : ℝ) : ℂ) := by
  unfold odlyzkoZeroRealSum
  simp_rw [odlyzkoPhi_conj_pair]
  rw [← Complex.ofReal_tsum, h.tsum_mul_left]

end
end TraceEuclidean
