import TraceEuclidean.OdlyzkoTiltedSech
import TraceEuclidean.PoitouFullKernel

/-!
# Positivity of the Poitou zero term in the open critical strip

For the degree-eleven test function, the explicit-formula zero term is the
Fourier transform of the full Poitou kernel after a real exponential tilt.
This module proves that its real part is nonnegative throughout the open
critical strip.  It removes the zero-term positivity condition from the
remaining degree-eleven explicit-formula input.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped ComplexConjugate Convolution RealInnerProductSpace

/-- The complete Poitou kernel with a real exponential weight. -/
def poitouTiltedFullKernel (y a x : ℝ) : ℂ :=
  ((Real.exp (a * x) * poitouFullKernel y x : ℝ) : ℂ)

theorem poitouTiltedFullKernel_eq_mul (y a x : ℝ) :
    poitouTiltedFullKernel y a x =
      poitouScaledTestComplex y x *
        TraceEuclidean.odlyzkoTiltedSech a x := by
  simp only [poitouTiltedFullKernel, poitouFullKernel,
    poitouScaledTestComplex, TraceEuclidean.odlyzkoTiltedSech]
  push_cast
  field_simp [(Real.cosh_pos (x / 2)).ne']

/-- Fourier multiplication becomes convolution for the tilted full kernel. -/
theorem poitouTiltedFullKernel_fourier_eq_convolution
    {y : ℝ} (hy : 0 < y) (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    𝓕 (poitouTiltedFullKernel y a) w =
      ((𝓕 (TraceEuclidean.odlyzkoTiltedSech a))
          ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 (poitouScaledTestComplex y))) w := by
  calc
    𝓕 (poitouTiltedFullKernel y a) w =
        𝓕 (fun x ↦ poitouScaledTestComplex y x *
          TraceEuclidean.odlyzkoTiltedSech a x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact poitouTiltedFullKernel_eq_mul y a x
    _ = _ := TraceEuclidean.fourierMulEqConvolution
      (poitouScaledTestComplex y)
      (TraceEuclidean.odlyzkoTiltedSech a)
      (poitouScaledTestComplex_integrable hy)
      (TraceEuclidean.odlyzkoTiltedSech_integrable a ha₁ ha₂)
      (TraceEuclidean.odlyzkoTiltedSech_fourier_integrable a ha₁ ha₂)
      (TraceEuclidean.odlyzkoTiltedSech_continuous a) w

private theorem poitouScaledTestFourier_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (𝓕 (poitouScaledTestComplex y)) := by
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (poitouScaledTestComplex_integrable hy)

theorem poitouTiltedFullKernel_convolution_integrable
    {y : ℝ} (hy : 0 < y) (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (fun z : ℝ ↦
      𝓕 (TraceEuclidean.odlyzkoTiltedSech a) z *
        𝓕 (poitouScaledTestComplex y) (w - z)) volume := by
  apply (TraceEuclidean.odlyzkoTiltedSech_fourier_integrable
    a ha₁ ha₂).mul_bdd
  · exact ((poitouScaledTestFourier_continuous hy).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with z
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
      (innerₗ ℝ) (poitouScaledTestComplex y) (w - z)

/-- The real part of the Poitou zero transform is nonnegative for every
exponential weight in the open critical strip. -/
theorem poitouTiltedFullKernel_fourier_re_nonneg
    {y : ℝ} (hy : 0 < y) (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    0 ≤ (𝓕 (poitouTiltedFullKernel y a) w).re := by
  rw [poitouTiltedFullKernel_fourier_eq_convolution hy a w ha₁ ha₂,
    MeasureTheory.convolution_mul]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re
    (poitouTiltedFullKernel_convolution_integrable hy a w ha₁ ha₂)]
  simp only [RCLike.re_eq_complex_re]
  apply integral_nonneg
  intro z
  change 0 ≤ (𝓕 (TraceEuclidean.odlyzkoTiltedSech a) z *
    𝓕 (poitouScaledTestComplex y) (w - z)).re
  rw [Complex.mul_re, poitouScaledTest_fourier_im_eq_zero hy]
  simp only [mul_zero, sub_zero]
  exact mul_nonneg
    (TraceEuclidean.odlyzkoTiltedSech_fourier_re_pos a z ha₁ ha₂).le
    (poitouScaledTest_fourier_re_nonneg hy (w - z))

/-- Poitou's zero transform in the source normalization. -/
def poitouPhi (y : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (poitouFullKernel y x : ℂ) *
    Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))

/-- The source complex parameter agrees with Lean's real-frequency Fourier
convention after subtracting the center of the critical strip. -/
theorem poitouPhi_eq_fourier (y : ℝ) (s : ℂ) :
    poitouPhi y s =
      𝓕 (poitouTiltedFullKernel y (s.re - 1 / 2))
        (-s.im / (2 * Real.pi)) := by
  rw [poitouPhi, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hexp :
      Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) =
        Complex.exp ((((s.re - 1 / 2) * x : ℝ) : ℂ)) *
          Complex.exp (((s.im * x : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext
    · norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re]
    · norm_num [Complex.mul_im, Complex.sub_im, Complex.add_im]
  have hfreq :
      ((-2 * Real.pi * x * (-s.im / (2 * Real.pi)) : ℝ) : ℂ) *
          Complex.I =
        ((s.im * x : ℝ) : ℂ) * Complex.I := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hexp, hfreq]
  have hrealexp :
      Complex.exp ((((s.re - 1 / 2) * x : ℝ) : ℂ)) =
        ((Real.exp ((s.re - 1 / 2) * x) : ℝ) : ℂ) := by
    exact (Complex.ofReal_exp _).symm
  rw [hrealexp]
  simp only [poitouTiltedFullKernel, Complex.ofReal_mul]
  ring

/-- Evenness of the full kernel gives reflection symmetry about the center of
the critical strip. -/
theorem poitouPhi_one_sub (y : ℝ) (s : ℂ) :
    poitouPhi y (1 - s) = poitouPhi y s := by
  unfold poitouPhi
  calc
    (∫ x : ℝ, (poitouFullKernel y x : ℂ) *
        Complex.exp (((1 - s) - (1 / 2 : ℂ)) * (x : ℂ))) =
      ∫ x : ℝ, (poitouFullKernel y (-x) : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * ((-x : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [poitouFullKernel_even]
      congr 1
      congr 1
      push_cast
      ring
    _ = ∫ x : ℝ, (poitouFullKernel y x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) := by
      exact integral_neg_eq_self
        (fun x : ℝ ↦ (poitouFullKernel y x : ℂ) *
          Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))) volume

/-- The Poitou transform commutes with complex conjugation. -/
theorem poitouPhi_conj (y : ℝ) (s : ℂ) :
    poitouPhi y (conj s) = conj (poitouPhi y s) := by
  unfold poitouPhi
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    map_sub, map_div₀, map_ofNat]
  simp

/-- The source-normalized Poitou zero transform is nonnegative throughout the
open critical strip. -/
theorem poitouPhi_re_nonneg_of_mem_open_strip
    {y : ℝ} (hy : 0 < y) (s : ℂ)
    (hs₁ : 0 < s.re) (hs₂ : s.re < 1) :
    0 ≤ (poitouPhi y s).re := by
  rw [poitouPhi_eq_fourier]
  apply poitouTiltedFullKernel_fourier_re_nonneg hy
  · linarith
  · linarith

/-- A summable family of nontrivial zero contributions has nonnegative total
real part.  The zero enumeration and its summability belong to the global
explicit-formula theorem. -/
theorem poitouPhi_zero_tsum_re_nonneg {y : ℝ} (hy : 0 < y)
    {I : Type*} (zeros : I → ℂ)
    (hstrip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1)
    (hsum : Summable (fun i ↦ poitouPhi y (zeros i))) :
    0 ≤ (∑' i, poitouPhi y (zeros i)).re := by
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg fun i ↦
    poitouPhi_re_nonneg_of_mem_open_strip hy (zeros i)
      (hstrip i).1 (hstrip i).2

end

end TraceEuclidean.PoitouKernel
