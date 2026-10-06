import TraceEuclidean.PoitouSmoothness
import TraceEuclidean.PoitouVariation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Gaussian regularization of the Poitou kernel

Poitou's noncompact kernel only has a bilateral Laplace transform in the
open critical strip.  Multiplication by `exp (-ε x²)` supplies an entire
regularization.  This module proves integrability of every exponential
moment, holomorphy of the regularized transform, and nonnegativity of its
zero contribution.  These are the analytic inputs for passing the completed
Dedekind-zeta contour formula to Poitou's limiting kernel.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped Convolution RealInnerProductSpace

def poitouGaussian (ε x : ℝ) : ℝ := Real.exp (-ε * x ^ 2)
def poitouGaussianComplex (ε x : ℝ) : ℂ := poitouGaussian ε x

theorem poitouGaussianComplex_eq (ε : ℝ) :
    poitouGaussianComplex ε =
      (fun x : ℝ ↦ Complex.exp (-(ε : ℂ) * (x : ℂ) ^ 2)) := by
  funext x
  simp [poitouGaussianComplex, poitouGaussian, Complex.ofReal_exp]

theorem poitouGaussian_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (poitouGaussian ε) volume := by
  unfold poitouGaussian
  convert integrable_exp_neg_mul_sq hε using 1

theorem poitouGaussianComplex_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (poitouGaussianComplex ε) volume :=
  (poitouGaussian_integrable hε).ofReal

theorem poitouGaussian_fourier_formula {ε : ℝ} (hε : 0 < ε) :
    𝓕 (poitouGaussianComplex ε) = fun w : ℝ ↦
      1 / ((ε / Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) / (ε / Real.pi : ℝ)) * (w : ℂ) ^ 2) := by
  rw [poitouGaussianComplex_eq]
  have hb : 0 < (((ε / Real.pi : ℝ) : ℂ)).re := by
    simp only [ofReal_re]
    positivity
  have h := fourier_gaussian_pi (b := ((ε / Real.pi : ℝ) : ℂ)) hb
  convert h using 1 <;> funext x
  · congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  · congr 2
    ring

theorem poitouGaussian_fourier_real_formula {ε : ℝ} (hε : 0 < ε) (w : ℝ) :
    𝓕 (poitouGaussianComplex ε) w =
      (((ε / Real.pi) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(Real.pi / (ε / Real.pi)) * w ^ 2) : ℝ) : ℂ) := by
  rw [poitouGaussian_fourier_formula hε]
  have hb : 0 < ε / Real.pi := div_pos hε Real.pi_pos
  change 1 / ((ε / Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      Complex.exp (-((Real.pi : ℂ) / (ε / Real.pi : ℝ)) * (w : ℂ) ^ 2) = _
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hhalf, ← Complex.ofReal_cpow hb.le]
  have harg :
      -((Real.pi : ℂ) / (ε / Real.pi : ℝ)) * (w : ℂ) ^ 2 =
        ((-(Real.pi / (ε / Real.pi)) * w ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  rw [Real.rpow_neg hb.le]
  simp [div_eq_mul_inv]

theorem poitouGaussian_continuous (ε : ℝ) : Continuous (poitouGaussian ε) := by
  unfold poitouGaussian
  fun_prop

theorem poitouGaussianComplex_continuous (ε : ℝ) :
    Continuous (poitouGaussianComplex ε) := by
  change Continuous (Complex.ofReal ∘ poitouGaussian ε)
  exact Complex.continuous_ofReal.comp (poitouGaussian_continuous ε)

theorem poitouGaussian_nonneg (ε x : ℝ) : 0 ≤ poitouGaussian ε x := by
  exact (Real.exp_pos _).le

theorem poitouGaussian_le_one {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    poitouGaussian ε x ≤ 1 := by
  rw [poitouGaussian, Real.exp_le_one_iff]
  nlinarith [mul_nonneg hε (sq_nonneg x)]

theorem poitouGaussian_fourier_re_nonneg {ε : ℝ} (hε : 0 < ε) (w : ℝ) :
    0 ≤ (𝓕 (poitouGaussianComplex ε) w).re := by
  rw [poitouGaussian_fourier_real_formula hε]
  simp only [ofReal_re]
  positivity

theorem poitouGaussian_fourier_im_eq_zero {ε : ℝ} (hε : 0 < ε) (w : ℝ) :
    (𝓕 (poitouGaussianComplex ε) w).im = 0 := by
  rw [poitouGaussian_fourier_real_formula hε]
  exact ofReal_im _

theorem poitouGaussian_fourier_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (𝓕 (poitouGaussianComplex ε)) volume := by
  let b : ℝ := Real.pi / (ε / Real.pi)
  let c : ℝ := (ε / Real.pi) ^ (-(1 / 2 : ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hbase : Integrable (fun w : ℝ ↦ c * Real.exp (-b * w ^ 2)) volume :=
    (integrable_exp_neg_mul_sq hb).const_mul c
  have hcomplex : Integrable
      (fun w : ℝ ↦ ((c * Real.exp (-b * w ^ 2) : ℝ) : ℂ)) volume :=
    hbase.ofReal
  apply hcomplex.congr
  filter_upwards with w
  rw [poitouGaussian_fourier_real_formula hε]

/-- Gaussian regularization of Poitou's complete kernel. -/
def poitouGaussianRegularizedKernel (y ε x : ℝ) : ℝ :=
  poitouFullKernel y x * poitouGaussian ε x

def poitouGaussianRegularizedKernelComplex (y ε x : ℝ) : ℂ :=
  poitouGaussianRegularizedKernel y ε x

theorem poitouGaussianRegularizedKernelComplex_eq_mul (y ε x : ℝ) :
    poitouGaussianRegularizedKernelComplex y ε x =
      poitouFullKernelComplex y x * poitouGaussianComplex ε x := by
  simp [poitouGaussianRegularizedKernelComplex, poitouGaussianRegularizedKernel,
    poitouFullKernelComplex, poitouGaussianComplex]

theorem poitouGaussianRegularizedKernelComplex_integrable
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) :
    Integrable (poitouGaussianRegularizedKernelComplex y ε) volume := by
  have heq : poitouGaussianRegularizedKernelComplex y ε =
      (fun x ↦ poitouFullKernelComplex y x * poitouGaussianComplex ε x) := by
    funext x
    exact poitouGaussianRegularizedKernelComplex_eq_mul y ε x
  rw [heq]
  apply (poitouFullKernelComplex_integrable hy).mul_bdd
  · exact (poitouGaussianComplex_continuous ε).aestronglyMeasurable
  · filter_upwards with x
    rw [poitouGaussianComplex, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poitouGaussian_nonneg ε x)]
    exact poitouGaussian_le_one hε.le x

theorem poitouGaussianRegularizedKernel_fourier_eq_convolution
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (w : ℝ) :
    𝓕 (poitouGaussianRegularizedKernelComplex y ε) w =
      ((𝓕 (poitouGaussianComplex ε)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 (poitouFullKernelComplex y))) w := by
  calc
    𝓕 (poitouGaussianRegularizedKernelComplex y ε) w =
        𝓕 (fun x ↦ poitouFullKernelComplex y x *
          poitouGaussianComplex ε x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact poitouGaussianRegularizedKernelComplex_eq_mul y ε x
    _ = _ := TraceEuclidean.fourierMulEqConvolution
      (poitouFullKernelComplex y) (poitouGaussianComplex ε)
      (poitouFullKernelComplex_integrable hy)
      (poitouGaussianComplex_integrable hε)
      (poitouGaussian_fourier_integrable hε)
      (poitouGaussianComplex_continuous ε) w

theorem poitouGaussianRegularizedKernel_convolution_integrable
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (w : ℝ) :
    Integrable (fun z : ℝ ↦
      𝓕 (poitouGaussianComplex ε) z *
        𝓕 (poitouFullKernelComplex y) (w - z)) volume := by
  apply (poitouGaussian_fourier_integrable hε).mul_bdd
  · exact ((VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (poitouFullKernelComplex_integrable hy)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with z
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
      (innerₗ ℝ) (poitouFullKernelComplex y) (w - z)

theorem poitouGaussianRegularizedKernel_fourier_re_nonneg
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (w : ℝ) :
    0 ≤ (𝓕 (poitouGaussianRegularizedKernelComplex y ε) w).re := by
  rw [poitouGaussianRegularizedKernel_fourier_eq_convolution hy hε w,
    MeasureTheory.convolution_mul]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re (poitouGaussianRegularizedKernel_convolution_integrable hy hε w)]
  simp only [RCLike.re_eq_complex_re]
  apply integral_nonneg
  intro z
  change 0 ≤ (𝓕 (poitouGaussianComplex ε) z *
    𝓕 (poitouFullKernelComplex y) (w - z)).re
  rw [Complex.mul_re, poitouGaussian_fourier_im_eq_zero hε,
    poitouFullKernel_fourier_im_eq_zero hy]
  simp only [zero_mul, sub_zero]
  exact mul_nonneg (poitouGaussian_fourier_re_nonneg hε z)
    (poitouFullKernel_fourier_re_nonneg hy (w - z))

theorem poitouGaussian_mul_exp_integrable {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ ↦ poitouGaussian ε x * Real.exp (t * x)) volume := by
  let a : ℝ := t / (2 * ε)
  let c : ℝ := Real.exp (t ^ 2 / (4 * ε))
  have hshift : Integrable (fun x : ℝ ↦ Real.exp (-ε * (x - a) ^ 2)) volume := by
    simpa only [sub_eq_add_neg] using
      (integrable_exp_neg_mul_sq hε).comp_add_right (-a)
  have hmajor : Integrable (fun x : ℝ ↦ c * Real.exp (-ε * (x - a) ^ 2)) volume :=
    hshift.const_mul c
  apply hmajor.congr
  filter_upwards with x
  rw [poitouGaussian, ← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  dsimp [a, c]
  field_simp [hε.ne']
  ring

theorem poitouFullKernel_le_nine_fourths (y x : ℝ) :
    poitouFullKernel y x ≤ 9 / 4 := by
  exact (div_le_self (poitouScaledTest_nonneg y x)
    (by simpa using Real.one_le_cosh (x / 2))).trans
      (poitouScaledTest_le_nine_fourths y x)

theorem poitouGaussianRegularizedKernel_nonneg (y ε x : ℝ) :
    0 ≤ poitouGaussianRegularizedKernel y ε x :=
  mul_nonneg (poitouFullKernel_nonneg y x) (poitouGaussian_nonneg ε x)

theorem poitouGaussianRegularizedKernel_continuous (y ε : ℝ) :
    Continuous (poitouGaussianRegularizedKernel y ε) :=
  (poitouFullKernel_continuous y).mul (poitouGaussian_continuous ε)

theorem poitouGaussianRegularizedKernel_exp_integrable
    {y ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x))
      ((volume : Measure ℝ).withDensity
        (fun x : ℝ ↦ ENNReal.ofReal (poitouGaussianRegularizedKernel y ε x))) := by
  let d : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (poitouGaussianRegularizedKernel y ε x)
  have hd : Measurable d :=
    (poitouGaussianRegularizedKernel_continuous y ε).measurable.ennreal_ofReal
  have hdtop : ∀ᵐ x ∂(volume : Measure ℝ), d x < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff hd hdtop]
  have hdreal (x : ℝ) : (d x).toReal = poitouGaussianRegularizedKernel y ε x := by
    simp [d, ENNReal.toReal_ofReal (poitouGaussianRegularizedKernel_nonneg y ε x)]
  simp_rw [hdreal]
  have hbase := (poitouGaussian_mul_exp_integrable hε t).const_mul (9 / 4 : ℝ)
  apply hbase.mono'
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (poitouGaussianRegularizedKernel_continuous y ε)).aestronglyMeasurable
  · filter_upwards with x
    have hfull := poitouFullKernel_le_nine_fourths y x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (poitouGaussianRegularizedKernel_nonneg y ε x))]
    calc
      Real.exp (t * x) * poitouGaussianRegularizedKernel y ε x =
          poitouFullKernel y x *
            (poitouGaussian ε x * Real.exp (t * x)) := by
        unfold poitouGaussianRegularizedKernel
        ring
      _ ≤ (9 / 4 : ℝ) *
          (poitouGaussian ε x * Real.exp (t * x)) :=
        mul_le_mul_of_nonneg_right hfull
          (mul_nonneg (poitouGaussian_nonneg ε x) (Real.exp_pos _).le)

def poitouGaussianRegularizedKernelMeasure (y ε : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x : ℝ ↦ ENNReal.ofReal (poitouGaussianRegularizedKernel y ε x))

theorem poitouGaussianRegularizedKernelMeasure_exp_integrable
    {y ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x))
      (poitouGaussianRegularizedKernelMeasure y ε) := by
  exact poitouGaussianRegularizedKernel_exp_integrable hε t

theorem poitouGaussianRegularizedKernelMeasure_integrableExpSet
    {y ε : ℝ} (hε : 0 < ε) :
    ProbabilityTheory.integrableExpSet id
      (poitouGaussianRegularizedKernelMeasure y ε) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact poitouGaussianRegularizedKernelMeasure_exp_integrable hε t

def poitouGaussianRegularizedPhi (y ε : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (poitouGaussianRegularizedKernel y ε x : ℂ) *
    Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))

theorem poitouGaussianRegularizedPhi_eq_complexMGF
    {y ε : ℝ} (s : ℂ) :
    poitouGaussianRegularizedPhi y ε s =
      ProbabilityTheory.complexMGF id (poitouGaussianRegularizedKernelMeasure y ε)
        (s - (1 / 2 : ℂ)) := by
  rw [poitouGaussianRegularizedPhi, ProbabilityTheory.complexMGF,
    poitouGaussianRegularizedKernelMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((poitouGaussianRegularizedKernel_continuous y ε).measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  simp [ENNReal.toReal_ofReal (poitouGaussianRegularizedKernel_nonneg y ε x)]

theorem poitouGaussianRegularizedPhi_differentiable
    {y ε : ℝ} (hε : 0 < ε) :
    Differentiable ℂ (poitouGaussianRegularizedPhi y ε) := by
  have hMGF : Differentiable ℂ
      (ProbabilityTheory.complexMGF id (poitouGaussianRegularizedKernelMeasure y ε)) := by
    intro z
    have hz : z.re ∈ interior
        (ProbabilityTheory.integrableExpSet id
          (poitouGaussianRegularizedKernelMeasure y ε)) := by
      rw [poitouGaussianRegularizedKernelMeasure_integrableExpSet hε]
      simp
    exact (ProbabilityTheory.hasDerivAt_complexMGF hz).differentiableAt
  have hshift : Differentiable ℂ (fun s : ℂ ↦ s - (1 / 2 : ℂ)) :=
    differentiable_id.sub (differentiable_const _)
  simpa only [Function.comp_def, ← poitouGaussianRegularizedPhi_eq_complexMGF] using
    hMGF.comp hshift

theorem poitouTiltedFullKernel_integrable
    {y a : ℝ} (hy : 0 < y)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (poitouTiltedFullKernel y a) volume := by
  have h := (TraceEuclidean.odlyzkoTiltedSech_integrable a ha₁ ha₂).mul_bdd
    (poitouScaledTestComplex_continuous y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      rw [poitouScaledTestComplex, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (poitouScaledTest_nonneg y x)]
      exact poitouScaledTest_le_nine_fourths y x)
  apply h.congr
  filter_upwards with x
  rw [poitouTiltedFullKernel_eq_mul]
  ring

def poitouGaussianRegularizedTiltedKernel (y ε a x : ℝ) : ℂ :=
  poitouTiltedFullKernel y a x * poitouGaussianComplex ε x

theorem poitouGaussianRegularizedTiltedKernel_integrable
    {y ε a : ℝ} (hy : 0 < y) (hε : 0 < ε)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (poitouGaussianRegularizedTiltedKernel y ε a) volume := by
  apply (poitouTiltedFullKernel_integrable hy ha₁ ha₂).mul_bdd
  · exact (poitouGaussianComplex_continuous ε).aestronglyMeasurable
  · filter_upwards with x
    rw [poitouGaussianComplex, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poitouGaussian_nonneg ε x)]
    exact poitouGaussian_le_one hε.le x

theorem poitouGaussianRegularizedTiltedKernel_fourier_eq_convolution
    {y ε a : ℝ} (hy : 0 < y) (hε : 0 < ε)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) (w : ℝ) :
    𝓕 (poitouGaussianRegularizedTiltedKernel y ε a) w =
      ((𝓕 (poitouGaussianComplex ε)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 (poitouTiltedFullKernel y a))) w := by
  exact TraceEuclidean.fourierMulEqConvolution
    (poitouTiltedFullKernel y a) (poitouGaussianComplex ε)
    (poitouTiltedFullKernel_integrable hy ha₁ ha₂)
    (poitouGaussianComplex_integrable hε)
    (poitouGaussian_fourier_integrable hε)
    (poitouGaussianComplex_continuous ε) w

theorem poitouGaussianRegularizedTiltedKernel_convolution_integrable
    {y ε a : ℝ} (hy : 0 < y) (hε : 0 < ε)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) (w : ℝ) :
    Integrable (fun z : ℝ ↦
      𝓕 (poitouGaussianComplex ε) z *
        𝓕 (poitouTiltedFullKernel y a) (w - z)) volume := by
  apply (poitouGaussian_fourier_integrable hε).mul_bdd
  · exact ((VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (poitouTiltedFullKernel_integrable hy ha₁ ha₂)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with z
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume
      (innerₗ ℝ) (poitouTiltedFullKernel y a) (w - z)

theorem poitouGaussianRegularizedTiltedKernel_fourier_re_nonneg
    {y ε a : ℝ} (hy : 0 < y) (hε : 0 < ε)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) (w : ℝ) :
    0 ≤ (𝓕 (poitouGaussianRegularizedTiltedKernel y ε a) w).re := by
  rw [poitouGaussianRegularizedTiltedKernel_fourier_eq_convolution
    hy hε ha₁ ha₂ w, MeasureTheory.convolution_mul]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re
    (poitouGaussianRegularizedTiltedKernel_convolution_integrable hy hε ha₁ ha₂ w)]
  simp only [RCLike.re_eq_complex_re]
  apply integral_nonneg
  intro z
  change 0 ≤ (𝓕 (poitouGaussianComplex ε) z *
    𝓕 (poitouTiltedFullKernel y a) (w - z)).re
  rw [Complex.mul_re, poitouGaussian_fourier_im_eq_zero hε]
  simp only [zero_mul, sub_zero]
  exact mul_nonneg (poitouGaussian_fourier_re_nonneg hε z)
    (poitouTiltedFullKernel_fourier_re_nonneg hy a (w - z) ha₁ ha₂)

theorem poitouGaussianRegularizedPhi_eq_fourier (y ε : ℝ) (s : ℂ) :
    poitouGaussianRegularizedPhi y ε s =
      𝓕 (poitouGaussianRegularizedTiltedKernel y ε (s.re - 1 / 2))
        (-s.im / (2 * Real.pi)) := by
  rw [poitouGaussianRegularizedPhi, Real.fourier_real_eq_integral_exp_smul]
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
        ((Real.exp ((s.re - 1 / 2) * x) : ℝ) : ℂ) :=
    (Complex.ofReal_exp _).symm
  rw [hrealexp]
  simp only [poitouGaussianRegularizedKernel, poitouGaussianRegularizedTiltedKernel,
    poitouTiltedFullKernel, poitouGaussianComplex, Complex.ofReal_mul]
  ring

theorem poitouGaussianRegularizedPhi_re_nonneg_of_mem_open_strip
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (s : ℂ)
    (hs₁ : 0 < s.re) (hs₂ : s.re < 1) :
    0 ≤ (poitouGaussianRegularizedPhi y ε s).re := by
  rw [poitouGaussianRegularizedPhi_eq_fourier]
  apply poitouGaussianRegularizedTiltedKernel_fourier_re_nonneg hy hε
  · linarith
  · linarith

end
end TraceEuclidean.PoitouKernel
