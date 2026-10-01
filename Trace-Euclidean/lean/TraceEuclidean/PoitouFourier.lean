import TraceEuclidean.PoitouBump
import TraceEuclidean.OdlyzkoFinalFourier

/-!
# Fourier representation of Poitou's test function

The compact quadratic bump has Fourier transform `poitouAmplitude (2 * π * w)`.
This module first proves the needed `L¹` bounds and the exact transform identity.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped Convolution RealInnerProductSpace

/-- Complex-valued form of Poitou's real amplitude. -/
def poitouAmplitudeComplex (x : ℝ) : ℂ := poitouAmplitude x

theorem poitouAmplitudeComplex_continuous : Continuous poitouAmplitudeComplex := by
  change Continuous (Complex.ofReal ∘ poitouAmplitude)
  exact Complex.continuous_ofReal.comp poitouAmplitude_continuous

private theorem poitouAmplitude_abs_le_majorant (x : ℝ) :
    |poitouAmplitude x| ≤ 24 / (1 + |x|) ^ 2 := by
  by_cases hx : |x| ≤ 1
  · have ha := poitouAmplitude_abs_le_three_halves x
    have hsum : 1 + |x| ≤ 2 := by linarith
    have hpow : (1 + |x|) ^ 2 ≤ 4 := by
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |x|) hsum 2]
    have hden : 0 < (1 + |x|) ^ 2 := by positivity
    have hmajor : (3 / 2 : ℝ) ≤ 24 / (1 + |x|) ^ 2 := by
      rw [le_div_iff₀ hden]
      nlinarith
    exact ha.trans hmajor
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    have ha := poitouAmplitude_abs_le_six_div_sq hx'
    have hxpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx'
    have hsum : 1 + |x| ≤ 2 * |x| := by linarith
    have hpow : (1 + |x|) ^ 2 ≤ 4 * |x| ^ 2 := by
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |x|) hsum 2]
    have hmajor : 6 / |x| ^ 2 ≤ 24 / (1 + |x|) ^ 2 := by
      rw [div_le_div_iff₀ (pow_pos hxpos 2)
        (by positivity : 0 < (1 + |x|) ^ 2)]
      nlinarith
    exact ha.trans hmajor

/-- The amplitude is integrable; its `x⁻²` decay is enough for Fourier
inversion of the compact bump. -/
theorem poitouAmplitudeComplex_integrable :
    Integrable poitouAmplitudeComplex volume := by
  have hbase : Integrable
      (fun x : ℝ ↦ 24 * (1 + ‖x‖) ^ (-(2 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (2 : ℝ)) (by norm_num)).const_mul 24
  have hmajor : (fun x : ℝ ↦ 24 / (1 + |x|) ^ 2) =
      (fun x : ℝ ↦ 24 * (1 + ‖x‖) ^ (-(2 : ℝ))) := by
    funext x
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
    norm_num [div_eq_mul_inv, Real.rpow_natCast]
  rw [← hmajor] at hbase
  apply hbase.mono' poitouAmplitudeComplex_continuous.aestronglyMeasurable
  filter_upwards with x
  rw [poitouAmplitudeComplex, norm_real, Real.norm_eq_abs]
  exact poitouAmplitude_abs_le_majorant x

private theorem poitouBumpComplex_fourier_real (w : ℝ) :
    𝓕 poitouBumpComplex w = ((𝓕 poitouBumpComplex w).re : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  calc
    (starRingEnd ℂ) (𝓕 poitouBumpComplex w) = 𝓕 poitouBumpComplex (-w) := by
      rw [Real.fourier_real_eq_integral_exp_smul,
        Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, map_mul, poitouBumpComplex, Complex.conj_ofReal,
        ← Complex.exp_conj, Complex.conj_I]
      congr 2
      push_cast
      ring
    _ = 𝓕 poitouBumpComplex w := by
      have hfun : poitouBumpComplex ∘ LinearIsometryEquiv.neg ℝ =
          poitouBumpComplex := by
        funext x
        exact poitouBumpComplex_even x
      have h := Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ) poitouBumpComplex w
      rw [hfun] at h
      simpa using h.symm

/-- The compact bump's mathlib-normalized Fourier transform is Poitou's
angular-frequency amplitude at `2πw`. -/
theorem poitouBump_fourier_eq_amplitude (w : ℝ) :
    𝓕 poitouBumpComplex w =
      (poitouAmplitude (2 * Real.pi * w) : ℂ) := by
  apply Complex.ext
  · rw [Real.fourier_real_eq_integral_exp_smul]
    have hint : Integrable
        (fun x : ℝ ↦ Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) •
          poitouBumpComplex x) volume := by
      apply poitouBump_integrable.norm.mono'
      · apply Continuous.aestronglyMeasurable
        exact (Complex.continuous_exp.comp (by fun_prop)).smul
          poitouBumpComplex_continuous
      · filter_upwards with x
        simp only [norm_smul, Complex.norm_exp, mul_re, ofReal_re, I_re,
          ofReal_im, I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
          one_mul]
        simp [poitouBumpComplex, Real.norm_eq_abs]
    change RCLike.re
        (∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) •
          poitouBumpComplex x) = poitouAmplitude (2 * Real.pi * w)
    rw [← integral_re hint, poitouAmplitude_eq_integral_bump_cos]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul, poitouBumpComplex]
    change (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
      (poitouBump x : ℂ)).re = poitouBump x * Real.cos (2 * Real.pi * w * x)
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [Complex.exp_ofReal_mul_I_re]
    rw [show -2 * Real.pi * x * w = -(2 * Real.pi * w * x) by ring,
      Real.cos_neg]
    ring
  · rw [poitouBumpComplex_fourier_real]
    simp

private theorem poitouBumpComplex_fourier_integrable :
    Integrable (𝓕 poitouBumpComplex) volume := by
  have hscaled : Integrable
      (fun w : ℝ ↦ poitouAmplitudeComplex ((2 * Real.pi) * w)) volume :=
    poitouAmplitudeComplex_integrable.comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  apply hscaled.congr
  filter_upwards with w
  rw [poitouBump_fourier_eq_amplitude]
  rfl

private theorem poitouBump_fourier_fourier_eq (w : ℝ) :
    𝓕 (𝓕 poitouBumpComplex) w = poitouBumpComplex w := by
  have hinv : 𝓕⁻ (𝓕 poitouBumpComplex) = poitouBumpComplex :=
    poitouBumpComplex_continuous.fourierInv_fourier_eq
      poitouBumpComplex_integrable poitouBumpComplex_fourier_integrable
  have hpoint := congrFun hinv (-w)
  rw [Real.fourierInv_eq_fourier_neg] at hpoint
  simpa [poitouBumpComplex_even] using hpoint

/-- Fourier inversion and scaling identify the transform of the amplitude
with the original compact bump. -/
theorem poitouAmplitude_fourier_eq_bump (w : ℝ) :
    𝓕 poitouAmplitudeComplex w =
      ((2 * Real.pi : ℝ) : ℂ) * poitouBumpComplex (2 * Real.pi * w) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcpos : 0 < c := by dsimp [c]; positivity
  rw [Real.fourier_real_eq]
  calc
    (∫ x : ℝ, 𝐞 (-(x * w)) • poitouAmplitudeComplex x) =
        ∫ x : ℝ, (fun y : ℝ ↦
          𝐞 (-(y * (c * w))) • (𝓕 poitouBumpComplex) y) (x / c) := by
      apply integral_congr_ae
      filter_upwards with x
      have hA := poitouBump_fourier_eq_amplitude (x / c)
      have hcx : c * (x / c) = x := by field_simp [hc]
      have htwo : 2 * Real.pi * (x / c) = x := by
        change c * (x / c) = x
        exact hcx
      change 𝐞 (-(x * w)) • (poitouAmplitude x : ℂ) = _
      rw [hA, htwo]
      congr 2
      field_simp [hc]
    _ = |c| • ∫ y : ℝ,
        𝐞 (-(y * (c * w))) • (𝓕 poitouBumpComplex) y :=
      Measure.integral_comp_div (fun y : ℝ ↦
        𝐞 (-(y * (c * w))) • (𝓕 poitouBumpComplex) y) c
    _ = ((c : ℝ) : ℂ) * 𝓕 (𝓕 poitouBumpComplex) (c * w) := by
      rw [abs_of_pos hcpos, Real.fourier_real_eq]
      rw [Complex.real_smul]
    _ = ((c : ℝ) : ℂ) * poitouBumpComplex (c * w) := by
      rw [poitouBump_fourier_fourier_eq]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        poitouBumpComplex (2 * Real.pi * w) := by rfl

private theorem poitouAmplitudeComplex_fourier_integrable :
    Integrable (𝓕 poitouAmplitudeComplex) volume := by
  have hscaled : Integrable
      (fun w : ℝ ↦ poitouBumpComplex ((2 * Real.pi) * w)) volume :=
    poitouBumpComplex_integrable.comp_mul_left'
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hmul := hscaled.const_mul (((2 * Real.pi : ℝ) : ℂ))
  apply hmul.congr
  filter_upwards with w
  exact (poitouAmplitude_fourier_eq_bump w).symm

theorem poitouAmplitude_fourier_re_nonneg (w : ℝ) :
    0 ≤ (𝓕 poitouAmplitudeComplex w).re := by
  rw [poitouAmplitude_fourier_eq_bump]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    poitouBumpComplex]
  exact mul_nonneg (by positivity) (poitouBump_nonneg _)

theorem poitouAmplitude_fourier_im_eq_zero (w : ℝ) :
    (𝓕 poitouAmplitudeComplex w).im = 0 := by
  rw [poitouAmplitude_fourier_eq_bump]
  simp [poitouBumpComplex]

/-- Complex-valued version of Poitou's nonnegative test function. -/
def poitouTestComplex (x : ℝ) : ℂ := poitouTest x

theorem poitouTestComplex_integrable : Integrable poitouTestComplex volume :=
  poitouTest_integrable.ofReal

theorem poitouTestComplex_continuous : Continuous poitouTestComplex := by
  change Continuous (Complex.ofReal ∘ poitouTest)
  exact Complex.continuous_ofReal.comp poitouTest_continuous

private theorem poitouTestComplex_eq_mul (x : ℝ) :
    poitouTestComplex x = poitouAmplitudeComplex x * poitouAmplitudeComplex x := by
  simp only [poitouTestComplex, poitouTest, poitouAmplitudeComplex, pow_two]
  push_cast
  rfl

/-- The transform of the squared amplitude is the convolution of the two
nonnegative compact-bump transforms. -/
theorem poitouTest_fourier_eq_convolution (w : ℝ) :
    𝓕 poitouTestComplex w =
      ((𝓕 poitouAmplitudeComplex) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 poitouAmplitudeComplex)) w := by
  calc
    𝓕 poitouTestComplex w =
        𝓕 (fun x ↦ poitouAmplitudeComplex x * poitouAmplitudeComplex x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact poitouTestComplex_eq_mul x
    _ = _ := TraceEuclidean.fourierMulEqConvolution
      poitouAmplitudeComplex poitouAmplitudeComplex
      poitouAmplitudeComplex_integrable poitouAmplitudeComplex_integrable
      poitouAmplitudeComplex_fourier_integrable
      poitouAmplitudeComplex_continuous w

theorem poitouTest_fourier_eq_nonnegativeIntegral (w : ℝ) :
    𝓕 poitouTestComplex w =
      ((∫ y : ℝ, (𝓕 poitouAmplitudeComplex y).re *
        (𝓕 poitouAmplitudeComplex (w - y)).re : ℝ) : ℂ) := by
  rw [poitouTest_fourier_eq_convolution, MeasureTheory.convolution_mul]
  calc
    (∫ y : ℝ, 𝓕 poitouAmplitudeComplex y *
        𝓕 poitouAmplitudeComplex (w - y)) =
        ∫ y : ℝ, (((𝓕 poitouAmplitudeComplex y).re *
          (𝓕 poitouAmplitudeComplex (w - y)).re : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      apply Complex.ext
      · simp only [mul_re, ofReal_re]
        rw [poitouAmplitude_fourier_im_eq_zero,
          poitouAmplitude_fourier_im_eq_zero]
        ring
      · simp only [mul_im, ofReal_im]
        rw [poitouAmplitude_fourier_im_eq_zero,
          poitouAmplitude_fourier_im_eq_zero]
        ring
    _ = ((∫ y : ℝ, (𝓕 poitouAmplitudeComplex y).re *
        (𝓕 poitouAmplitudeComplex (w - y)).re : ℝ) : ℂ) := integral_ofReal

/-- Poitou's source test has a nonnegative Fourier transform. -/
theorem poitouTest_fourier_re_nonneg (w : ℝ) :
    0 ≤ (𝓕 poitouTestComplex w).re := by
  rw [poitouTest_fourier_eq_nonnegativeIntegral]
  simp only [ofReal_re]
  exact integral_nonneg fun y ↦ mul_nonneg
    (poitouAmplitude_fourier_re_nonneg y)
    (poitouAmplitude_fourier_re_nonneg (w - y))

theorem poitouTest_fourier_im_eq_zero (w : ℝ) :
    (𝓕 poitouTestComplex w).im = 0 := by
  rw [poitouTest_fourier_eq_nonnegativeIntegral]
  exact ofReal_im _

private theorem poitouBump_scaled_sq_integral :
    (∫ y : ℝ, poitouBump (2 * Real.pi * y) ^ 2) =
      3 / (10 * Real.pi) := by
  let c : ℝ := 2 * Real.pi
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hscale := Measure.integral_comp_mul_left
    (fun t : ℝ ↦ poitouBump t ^ 2) c
  change (∫ y : ℝ, poitouBump (c * y) ^ 2) = _
  rw [hscale, poitouBump_sq_integral, abs_of_pos (inv_pos.mpr hcpos)]
  change c⁻¹ * (3 / 5 : ℝ) = 3 / (10 * Real.pi)
  dsimp [c]
  field_simp [Real.pi_ne_zero]
  ring

/-- The full-line mass of Poitou's test is `6π/5`. -/
theorem poitouTest_integral_univ :
    (∫ x : ℝ, poitouTest x) = 6 * Real.pi / 5 := by
  have hzero : 𝓕 poitouTestComplex 0 =
      ((6 * Real.pi / 5 : ℝ) : ℂ) := by
    rw [poitouTest_fourier_eq_convolution, MeasureTheory.convolution_mul]
    simp_rw [poitouAmplitude_fourier_eq_bump]
    calc
      (∫ y : ℝ,
          ((2 * Real.pi : ℝ) : ℂ) * poitouBumpComplex (2 * Real.pi * y) *
            (((2 * Real.pi : ℝ) : ℂ) *
              poitouBumpComplex (2 * Real.pi * (0 - y)))) =
          ∫ y : ℝ, (((2 * Real.pi) ^ 2 *
            poitouBump (2 * Real.pi * y) ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [show 2 * Real.pi * (0 - y) = -(2 * Real.pi * y) by ring,
          poitouBumpComplex_even]
        simp only [poitouBumpComplex]
        push_cast
        ring
      _ = ((∫ y : ℝ, (2 * Real.pi) ^ 2 *
          poitouBump (2 * Real.pi * y) ^ 2 : ℝ) : ℂ) := integral_ofReal
      _ = (((2 * Real.pi) ^ 2 *
          (∫ y : ℝ, poitouBump (2 * Real.pi * y) ^ 2) : ℝ) : ℂ) := by
        rw [integral_const_mul]
      _ = ((6 * Real.pi / 5 : ℝ) : ℂ) := by
        rw [poitouBump_scaled_sq_integral]
        congr 1
        field_simp [Real.pi_ne_zero]
        ring
  have hfourierIntegral : 𝓕 poitouTestComplex 0 =
      ((∫ x : ℝ, poitouTest x : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, zero_mul, ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul, poitouTestComplex]
    exact integral_ofReal
  rw [hfourierIntegral] at hzero
  exact Complex.ofReal_injective hzero

/-- Poitou's positive-half-line mass is the source value `3π/5`. -/
theorem poitouTest_integral_Ioi :
    (∫ x in Set.Ioi (0 : ℝ), poitouTest x) = 3 * Real.pi / 5 := by
  have hleft : (∫ x in Set.Iic (0 : ℝ), poitouTest x) =
      ∫ x in Set.Ioi (0 : ℝ), poitouTest x := by
    calc
      (∫ x in Set.Iic (0 : ℝ), poitouTest x) =
          ∫ x in Set.Iic (0 : ℝ), poitouTest (-x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x _
        exact (poitouTest_even x).symm
      _ = ∫ x in Set.Ioi (0 : ℝ), poitouTest x := by
        simpa using integral_comp_neg_Iic (0 : ℝ) poitouTest
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) poitouTest_integrable.integrableOn
      poitouTest_integrable.integrableOn
  rw [hleft, poitouTest_integral_univ] at hsplit
  linarith

end

end TraceEuclidean.PoitouKernel
