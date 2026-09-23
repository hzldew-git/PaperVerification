import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import TraceEuclidean.V15OdlyzkoSechFourier

/-!
# Fourier positivity of Odlyzko's complete `b = 4` test function

This file combines the compactly supported factor `H(x / 4)` with the
hyperbolic-secant factor.  A product-to-convolution argument reduces the
Fourier transform of the complete test function to the convolution of two
real nonnegative Fourier transforms.  It follows that the transform is real
and nonnegative at every real frequency.
-/

namespace TraceEuclidean

open MeasureTheory FourierTransform Complex
open scoped Convolution RealInnerProductSpace

noncomputable section

theorem v15FourierMulEqConvolution
    (f g : ℝ → ℂ) (hf : Integrable f volume) (hg : Integrable g volume)
    (hFg : Integrable (𝓕 g) volume) (hgc : Continuous g) (w : ℝ) :
    𝓕 (fun x ↦ f x * g x) w =
      ((𝓕 g) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 f)) w := by
  let K : ℝ → ℝ → ℂ := fun x y ↦
    (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
      Complex.exp ((↑(2 * Real.pi * y * x) : ℂ) * Complex.I)) * (f x * 𝓕 g y)
  have hK : Integrable (Function.uncurry K) (volume.prod volume) := by
    apply Integrable.mono' (hf.norm.mul_prod hFg.norm)
    · have hbase : AEStronglyMeasurable
          (fun p : ℝ × ℝ ↦ f p.1 * 𝓕 g p.2) (volume.prod volume) :=
        (hf.mul_prod hFg).aestronglyMeasurable
      have hphase : AEStronglyMeasurable
          (fun p : ℝ × ℝ ↦
            Complex.exp ((↑(-2 * Real.pi * p.1 * w) : ℂ) * Complex.I) *
              Complex.exp ((↑(2 * Real.pi * p.2 * p.1) : ℂ) * Complex.I))
          (volume.prod volume) := by
        apply Continuous.aestronglyMeasurable
        fun_prop
      exact hphase.mul hbase
    · filter_upwards with p
      rcases p with ⟨x, y⟩
      dsimp only [K, Function.uncurry_apply_pair]
      simp only [norm_mul, Complex.norm_exp, mul_re, ofReal_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero, Real.exp_zero, one_mul]
      exact le_rfl
  have hInv : 𝓕⁻ (𝓕 g) = g := hgc.fourierInv_fourier_eq hg hFg
  have hInvInt (x : ℝ) :
      g x = ∫ y : ℝ,
        Complex.exp ((↑(2 * Real.pi * y * x) : ℂ) * Complex.I) * 𝓕 g y := by
    calc
      g x = 𝓕⁻ (𝓕 g) x := congrFun hInv.symm x
      _ = _ := by
        rw [Real.fourierInv_eq']
        simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
        apply integral_congr_ae
        filter_upwards with y
        congr 2
        push_cast
        ring
  have hFf (a : ℝ) :
      𝓕 f a = ∫ x : ℝ,
        Complex.exp ((↑(-2 * Real.pi * x * a) : ℂ) * Complex.I) * f x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
  rw [Real.fourier_real_eq_integral_exp_smul, MeasureTheory.convolution_mul]
  simp only [smul_eq_mul]
  calc
    (∫ x : ℝ, Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
        (f x * g x)) =
        ∫ x : ℝ, ∫ y : ℝ, K x y := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hInvInt]
      rw [show Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
          (f x * ∫ y : ℝ,
            Complex.exp ((↑(2 * Real.pi * y * x) : ℂ) * Complex.I) * 𝓕 g y) =
          (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) * f x) *
            ∫ y : ℝ,
              Complex.exp ((↑(2 * Real.pi * y * x) : ℂ) * Complex.I) * 𝓕 g y by ring,
        ← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [K]
      ring
    _ = ∫ y : ℝ, ∫ x : ℝ, K x y := integral_integral_swap hK
    _ = ∫ y : ℝ, 𝓕 g y * 𝓕 f (w - y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hFf, ← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [K]
      calc
        (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
            Complex.exp ((↑(2 * Real.pi * y * x) : ℂ) * Complex.I)) * (f x * 𝓕 g y) =
            𝓕 g y *
              ((Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
                Complex.exp ((↑(2 * Real.pi * y * x) : ℂ) * Complex.I)) * f x) := by ring
        _ = 𝓕 g y *
              (Complex.exp ((↑(-2 * Real.pi * x * (w - y)) : ℂ) * Complex.I) * f x) := by
          rw [← Complex.exp_add]
          congr 3
          push_cast
          ring

/-- The complete `b = 4` test function, viewed as a complex-valued function. -/
def v15OdlyzkoF4Complex (x : ℝ) : ℂ := v15OdlyzkoF4 x

theorem v15OdlyzkoF4Complex_continuous : Continuous v15OdlyzkoF4Complex := by
  change Continuous (Complex.ofReal ∘ v15OdlyzkoF4)
  exact Complex.continuous_ofReal.comp v15OdlyzkoF4_continuous

theorem v15OdlyzkoF4Complex_integrable : Integrable v15OdlyzkoF4Complex volume := by
  exact v15OdlyzkoF4_integrable.ofReal

theorem v15OdlyzkoF4Complex_eq_mul (x : ℝ) :
    v15OdlyzkoF4Complex x =
      v15OdlyzkoH4Complex x * v15OdlyzkoSechComplex x := by
  simp only [v15OdlyzkoF4Complex, v15OdlyzkoF4, v15OdlyzkoH4Complex,
    v15OdlyzkoHComplex, v15OdlyzkoSechComplex, v15OdlyzkoSech]
  push_cast
  ring

/-- The Fourier transform of the complete test function is the convolution
of the transforms of its two factors. -/
theorem v15OdlyzkoF4_fourier_eq_convolution (w : ℝ) :
    𝓕 v15OdlyzkoF4Complex w =
      ((𝓕 v15OdlyzkoSechComplex) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 v15OdlyzkoH4Complex)) w := by
  calc
    𝓕 v15OdlyzkoF4Complex w =
        𝓕 (fun x ↦ v15OdlyzkoH4Complex x * v15OdlyzkoSechComplex x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact v15OdlyzkoF4Complex_eq_mul x
    _ = _ := v15FourierMulEqConvolution
      v15OdlyzkoH4Complex v15OdlyzkoSechComplex
      v15OdlyzkoH4Complex_integrable v15OdlyzkoSechComplex_integrable
      v15OdlyzkoSechFourier_integrable v15OdlyzkoSechComplex_continuous w

private theorem v15OdlyzkoH4Fourier_continuous :
    Continuous (𝓕 v15OdlyzkoH4Complex) := by
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ v15OdlyzkoH4Complex_integrable

theorem v15OdlyzkoF4_fourierConvolution_integrable (w : ℝ) :
    Integrable (fun y : ℝ ↦
      𝓕 v15OdlyzkoSechComplex y * 𝓕 v15OdlyzkoH4Complex (w - y)) volume := by
  apply v15OdlyzkoSechFourier_integrable.mul_bdd
  · exact (v15OdlyzkoH4Fourier_continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with y
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      v15OdlyzkoH4Complex (w - y)

/-- An exact real-integral form of the Fourier transform.  Its integrand is
pointwise nonnegative. -/
theorem v15OdlyzkoF4_fourier_eq_nonnegativeIntegral (w : ℝ) :
    𝓕 v15OdlyzkoF4Complex w =
      ((∫ y : ℝ, (𝓕 v15OdlyzkoSechComplex y).re *
        (𝓕 v15OdlyzkoH4Complex (w - y)).re : ℝ) : ℂ) := by
  rw [v15OdlyzkoF4_fourier_eq_convolution, MeasureTheory.convolution_mul]
  calc
    (∫ y : ℝ, 𝓕 v15OdlyzkoSechComplex y *
        𝓕 v15OdlyzkoH4Complex (w - y)) =
        ∫ y : ℝ, (((𝓕 v15OdlyzkoSechComplex y).re *
          (𝓕 v15OdlyzkoH4Complex (w - y)).re : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      apply Complex.ext
      · simp only [mul_re, ofReal_re]
        rw [v15OdlyzkoSechFourierImEqZero, v15OdlyzkoH4_fourier_im_eq_zero]
        ring
      · simp only [mul_im, ofReal_im]
        rw [v15OdlyzkoSechFourierImEqZero, v15OdlyzkoH4_fourier_im_eq_zero]
        ring
    _ = ((∫ y : ℝ, (𝓕 v15OdlyzkoSechComplex y).re *
        (𝓕 v15OdlyzkoH4Complex (w - y)).re : ℝ) : ℂ) := integral_ofReal

/-- The Fourier transform of Odlyzko's complete unconditional `b = 4` test
function has nonnegative real part at every real frequency. -/
theorem v15OdlyzkoF4_fourier_re_nonneg (w : ℝ) :
    0 ≤ (𝓕 v15OdlyzkoF4Complex w).re := by
  rw [v15OdlyzkoF4_fourier_eq_nonnegativeIntegral]
  simp only [ofReal_re]
  exact integral_nonneg fun y ↦ mul_nonneg
    (v15OdlyzkoSechFourierRePos y).le
    (v15OdlyzkoH4_fourier_re_nonneg (w - y))

/-- The Fourier transform of Odlyzko's complete unconditional `b = 4` test
function is real at every real frequency. -/
theorem v15OdlyzkoF4_fourier_im_eq_zero (w : ℝ) :
    (𝓕 v15OdlyzkoF4Complex w).im = 0 := by
  rw [v15OdlyzkoF4_fourier_eq_nonnegativeIntegral]
  exact ofReal_im _

end
end TraceEuclidean
