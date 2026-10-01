import TraceEuclidean.PoitouFourier
import TraceEuclidean.PoitouDegreeEleven
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The full Poitou kernel for the degree-eleven parameter

Poitou's explicit formula uses `f(√y x) / cosh(x/2)`, where `f` is the
nonnegative test function constructed in `PoitouKernel`.  This module
proves the elementary analytic and Fourier-positive properties of that full
kernel and derives the exact endpoint correction `12π / (5 n √y)`.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped Convolution RealInnerProductSpace
open TraceEuclidean.PoitouDegreeEleven

/-- Poitou's scaled auxiliary function. -/
def poitouScaledTest (y x : ℝ) : ℝ :=
  poitouTest (Real.sqrt y * x)

/-- The complete source kernel, including the hyperbolic-secant factor. -/
def poitouFullKernel (y x : ℝ) : ℝ :=
  poitouScaledTest y x / Real.cosh (x / 2)

theorem poitouScaledTest_even (y x : ℝ) :
    poitouScaledTest y (-x) = poitouScaledTest y x := by
  rw [poitouScaledTest, poitouScaledTest,
    show Real.sqrt y * -x = -(Real.sqrt y * x) by ring,
    poitouTest_even]

theorem poitouScaledTest_nonneg (y x : ℝ) :
    0 ≤ poitouScaledTest y x := poitouTest_nonneg _

theorem poitouScaledTest_continuous (y : ℝ) :
    Continuous (poitouScaledTest y) := by
  unfold poitouScaledTest
  exact poitouTest_continuous.comp (continuous_const.mul continuous_id)

@[simp] theorem poitouScaledTest_zero (y : ℝ) : poitouScaledTest y 0 = 1 := by
  simp [poitouScaledTest]

theorem poitouFullKernel_even (y x : ℝ) :
    poitouFullKernel y (-x) = poitouFullKernel y x := by
  rw [poitouFullKernel, poitouFullKernel, poitouScaledTest_even,
    show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

theorem poitouFullKernel_nonneg (y x : ℝ) :
    0 ≤ poitouFullKernel y x :=
  div_nonneg (poitouScaledTest_nonneg y x) (Real.cosh_pos (x / 2)).le

theorem poitouFullKernel_continuous (y : ℝ) :
    Continuous (poitouFullKernel y) := by
  unfold poitouFullKernel
  exact (poitouScaledTest_continuous y).div
    (Real.continuous_cosh.comp (continuous_id.div_const 2))
    (fun x ↦ (Real.cosh_pos (x / 2)).ne')

@[simp] theorem poitouFullKernel_zero (y : ℝ) : poitouFullKernel y 0 = 1 := by
  simp [poitouFullKernel]

theorem poitouScaledTest_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (poitouScaledTest y) volume := by
  have hsqrt : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  change Integrable (fun x : ℝ ↦ poitouTest (Real.sqrt y * x)) volume
  exact poitouTest_integrable.comp_mul_left' hsqrt

theorem poitouFullKernel_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (poitouFullKernel y) volume := by
  apply (poitouScaledTest_integrable hy).mono'
  · exact (poitouFullKernel_continuous y).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (poitouFullKernel_nonneg y x)]
    unfold poitouFullKernel
    exact div_le_self (poitouScaledTest_nonneg y x)
      (by simpa using Real.one_le_cosh (x / 2))

/-- Complex form of the scaled auxiliary function. -/
def poitouScaledTestComplex (y x : ℝ) : ℂ := poitouScaledTest y x

theorem poitouScaledTestComplex_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (poitouScaledTestComplex y) volume :=
  (poitouScaledTest_integrable hy).ofReal

theorem poitouScaledTestComplex_continuous (y : ℝ) :
    Continuous (poitouScaledTestComplex y) := by
  change Continuous (Complex.ofReal ∘ poitouScaledTest y)
  exact Complex.continuous_ofReal.comp (poitouScaledTest_continuous y)

theorem poitouScaledTest_fourier_eq {y w : ℝ} (hy : 0 < y) :
    𝓕 (poitouScaledTestComplex y) w =
      (((Real.sqrt y)⁻¹ : ℝ) : ℂ) *
        𝓕 poitouTestComplex (w / Real.sqrt y) := by
  let a := Real.sqrt y
  have ha : 0 < a := Real.sqrt_pos.2 hy
  rw [Real.fourier_real_eq]
  calc
    (∫ x : ℝ, 𝐞 (-(x * w)) • poitouScaledTestComplex y x) =
        ∫ x : ℝ, (fun u : ℝ ↦
          𝐞 (-(u * (w / a))) • poitouTestComplex u) (a * x) := by
      apply integral_congr_ae
      filter_upwards with x
      change 𝐞 (-(x * w)) • (poitouTest (a * x) : ℂ) = _
      congr 2
      field_simp [ha.ne']
    _ = |a⁻¹| • ∫ u : ℝ,
        𝐞 (-(u * (w / a))) • poitouTestComplex u :=
      Measure.integral_comp_mul_left (fun u : ℝ ↦
        𝐞 (-(u * (w / a))) • poitouTestComplex u) a
    _ = ((a⁻¹ : ℝ) : ℂ) * 𝓕 poitouTestComplex (w / a) := by
      rw [abs_of_pos (inv_pos.mpr ha), Real.fourier_real_eq,
        Complex.real_smul]
    _ = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) *
        𝓕 poitouTestComplex (w / Real.sqrt y) := by
      dsimp [a]

theorem poitouScaledTest_fourier_re_nonneg {y : ℝ} (hy : 0 < y) (w : ℝ) :
    0 ≤ (𝓕 (poitouScaledTestComplex y) w).re := by
  rw [poitouScaledTest_fourier_eq hy]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity)
    (poitouTest_fourier_re_nonneg (w / Real.sqrt y))

theorem poitouScaledTest_fourier_im_eq_zero {y : ℝ} (hy : 0 < y) (w : ℝ) :
    (𝓕 (poitouScaledTestComplex y) w).im = 0 := by
  rw [poitouScaledTest_fourier_eq hy]
  simp [poitouTest_fourier_im_eq_zero]

/-- Complex form of the full Poitou kernel. -/
def poitouFullKernelComplex (y x : ℝ) : ℂ := poitouFullKernel y x

theorem poitouFullKernelComplex_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (poitouFullKernelComplex y) volume :=
  (poitouFullKernel_integrable hy).ofReal

theorem poitouFullKernelComplex_continuous (y : ℝ) :
    Continuous (poitouFullKernelComplex y) := by
  change Continuous (Complex.ofReal ∘ poitouFullKernel y)
  exact Complex.continuous_ofReal.comp (poitouFullKernel_continuous y)

private theorem poitouFullKernelComplex_eq_mul (y x : ℝ) :
    poitouFullKernelComplex y x =
      poitouScaledTestComplex y x * TraceEuclidean.odlyzkoSechComplex x := by
  simp only [poitouFullKernelComplex, poitouFullKernel, poitouScaledTestComplex,
    TraceEuclidean.odlyzkoSechComplex, TraceEuclidean.odlyzkoSech]
  push_cast
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem poitouFullKernel_fourier_eq_convolution {y : ℝ} (hy : 0 < y) (w : ℝ) :
    𝓕 (poitouFullKernelComplex y) w =
      ((𝓕 TraceEuclidean.odlyzkoSechComplex) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 (poitouScaledTestComplex y))) w := by
  calc
    𝓕 (poitouFullKernelComplex y) w =
        𝓕 (fun x ↦ poitouScaledTestComplex y x *
          TraceEuclidean.odlyzkoSechComplex x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact poitouFullKernelComplex_eq_mul y x
    _ = _ := TraceEuclidean.fourierMulEqConvolution
      (poitouScaledTestComplex y) TraceEuclidean.odlyzkoSechComplex
      (poitouScaledTestComplex_integrable hy)
      TraceEuclidean.odlyzkoSechComplex_integrable
      TraceEuclidean.odlyzkoSechFourier_integrable
      TraceEuclidean.odlyzkoSechComplex_continuous w

theorem poitouFullKernel_fourier_re_nonneg {y : ℝ} (hy : 0 < y) (w : ℝ) :
    0 ≤ (𝓕 (poitouFullKernelComplex y) w).re := by
  rw [poitouFullKernel_fourier_eq_convolution hy,
    MeasureTheory.convolution_mul]
  have hint : Integrable (fun z : ℝ ↦
      𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)) volume := by
    apply TraceEuclidean.odlyzkoSechFourier_integrable.mul_bdd
    · exact (VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (innerSL ℝ).continuous₂
        (poitouScaledTestComplex_integrable hy)).comp
          (continuous_const.sub continuous_id) |>.aestronglyMeasurable
    · filter_upwards with z
      exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
        (innerₗ ℝ) (poitouScaledTestComplex y) (w - z)
  have hnonneg : (0 : ℝ) ≤ ∫ z : ℝ,
      (𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)).re :=
    integral_nonneg fun z ↦ by
    rw [mul_re, TraceEuclidean.odlyzkoSechFourierImEqZero,
      poitouScaledTest_fourier_im_eq_zero hy]
    simp only [zero_mul, sub_zero]
    exact mul_nonneg (TraceEuclidean.odlyzkoSechFourierRePos z).le
      (poitouScaledTest_fourier_re_nonneg hy (w - z))
  have hre : (∫ z : ℝ,
      (𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)).re) =
      (∫ z : ℝ, 𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)).re := by
    convert integral_re hint using 1 <;> with_reducible_and_instances rfl
  rw [hre] at hnonneg
  exact hnonneg

theorem poitouFullKernel_fourier_im_eq_zero {y : ℝ} (hy : 0 < y) (w : ℝ) :
    (𝓕 (poitouFullKernelComplex y) w).im = 0 := by
  rw [poitouFullKernel_fourier_eq_convolution hy,
    MeasureTheory.convolution_mul]
  have hint : Integrable (fun z : ℝ ↦
      𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)) volume := by
    apply TraceEuclidean.odlyzkoSechFourier_integrable.mul_bdd
    · exact (VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar (innerSL ℝ).continuous₂
        (poitouScaledTestComplex_integrable hy)).comp
          (continuous_const.sub continuous_id) |>.aestronglyMeasurable
    · filter_upwards with z
      exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
        (innerₗ ℝ) (poitouScaledTestComplex y) (w - z)
  have hzero : (∫ z : ℝ,
      (𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)).im) = (0 : ℝ) := by
    apply integral_eq_zero_of_ae
    filter_upwards with z
    rw [mul_im, TraceEuclidean.odlyzkoSechFourierImEqZero,
      poitouScaledTest_fourier_im_eq_zero hy]
    norm_num
  have him : (∫ z : ℝ,
      (𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)).im) =
      (∫ z : ℝ, 𝓕 TraceEuclidean.odlyzkoSechComplex z *
        𝓕 (poitouScaledTestComplex y) (w - z)).im := by
    convert integral_im hint using 1 <;> with_reducible_and_instances rfl
  rw [him] at hzero
  exact hzero

/-- Exact positive-half-line area after scaling. -/
theorem poitouScaledTest_integral_Ioi {y : ℝ} (hy : 0 < y) :
    (∫ x in Set.Ioi (0 : ℝ), poitouScaledTest y x) =
      3 * Real.pi / (5 * Real.sqrt y) := by
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  change (∫ x in Set.Ioi (0 : ℝ),
    poitouTest (Real.sqrt y * x)) = _
  have hscale := integral_comp_mul_left_Ioi poitouTest 0 hsqrt
  rw [mul_zero, poitouTest_integral_Ioi] at hscale
  rw [hscale]
  simp only [smul_eq_mul]
  field_simp [hsqrt.ne']

/-- The endpoint term in degree `n` is exactly Poitou's
`12π / (5 n √y)`. -/
theorem poitouEndpointCorrection (n : ℕ) {y : ℝ} (hy : 0 < y) :
    4 / (n : ℝ) * (∫ x in Set.Ioi (0 : ℝ), poitouScaledTest y x) =
      12 * Real.pi / (5 * (n : ℝ) * Real.sqrt y) := by
  rw [poitouScaledTest_integral_Ioi hy]
  ring

end

end TraceEuclidean.PoitouKernel
