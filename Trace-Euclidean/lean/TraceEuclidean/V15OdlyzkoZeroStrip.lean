import TraceEuclidean.V15OdlyzkoFinalFourier
import TraceEuclidean.V15OdlyzkoTiltedSech

/-!
# Positivity of the Odlyzko zero term in the open critical strip

The explicit formula tests the transform after multiplication by a real
exponential weight.  This module proves nonnegativity for every weight in the
open strip.  The boundary weights are handled separately below.
-/

namespace TraceEuclidean

open MeasureTheory FourierTransform Complex
open scoped Convolution RealInnerProductSpace

noncomputable section

/-- The complete test function with a real exponential weight. -/
def v15OdlyzkoTiltedF4 (a x : ℝ) : ℂ :=
  ((Real.exp (a * x) * v15OdlyzkoF4 x : ℝ) : ℂ)

theorem v15OdlyzkoTiltedF4_continuous (a : ℝ) :
    Continuous (v15OdlyzkoTiltedF4 a) := by
  change Continuous (Complex.ofReal ∘
    fun x : ℝ ↦ Real.exp (a * x) * v15OdlyzkoF4 x)
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      v15OdlyzkoF4_continuous)

theorem v15OdlyzkoTiltedF4_hasCompactSupport (a : ℝ) :
    HasCompactSupport (v15OdlyzkoTiltedF4 a) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-8) 8) isCompact_Icc
  intro x hx
  change -8 ≤ x ∧ x ≤ 8
  rw [← abs_le]
  by_contra hbound
  apply hx
  rw [v15OdlyzkoTiltedF4,
    v15OdlyzkoF4_eq_zero_of_eight_lt_abs (lt_of_not_ge hbound), mul_zero]
  rfl

theorem v15OdlyzkoTiltedF4_integrable (a : ℝ) :
    Integrable (v15OdlyzkoTiltedF4 a) volume :=
  (v15OdlyzkoTiltedF4_continuous a).integrable_of_hasCompactSupport
    (v15OdlyzkoTiltedF4_hasCompactSupport a)

theorem v15OdlyzkoTiltedF4_eq_mul (a x : ℝ) :
    v15OdlyzkoTiltedF4 a x =
      v15OdlyzkoH4Complex x * v15OdlyzkoTiltedSech a x := by
  simp only [v15OdlyzkoTiltedF4, v15OdlyzkoF4,
    v15OdlyzkoH4Complex, v15OdlyzkoHComplex,
    v15OdlyzkoTiltedSech]
  push_cast
  ring

theorem v15OdlyzkoTiltedF4_fourier_eq_convolution (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    𝓕 (v15OdlyzkoTiltedF4 a) w =
      ((𝓕 (v15OdlyzkoTiltedSech a)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (𝓕 v15OdlyzkoH4Complex)) w := by
  calc
    𝓕 (v15OdlyzkoTiltedF4 a) w =
        𝓕 (fun x ↦ v15OdlyzkoH4Complex x *
          v15OdlyzkoTiltedSech a x) w := by
      apply Real.fourier_congr_ae
      filter_upwards with x
      exact v15OdlyzkoTiltedF4_eq_mul a x
    _ = _ := v15FourierMulEqConvolution
      v15OdlyzkoH4Complex (v15OdlyzkoTiltedSech a)
      v15OdlyzkoH4Complex_integrable
      (v15OdlyzkoTiltedSech_integrable a ha₁ ha₂)
      (v15OdlyzkoTiltedSech_fourier_integrable a ha₁ ha₂)
      (v15OdlyzkoTiltedSech_continuous a) w

private theorem v15OdlyzkoH4Fourier_continuous :
    Continuous (𝓕 v15OdlyzkoH4Complex) := by
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ v15OdlyzkoH4Complex_integrable

theorem v15OdlyzkoTiltedF4_convolution_integrable (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    Integrable (fun y : ℝ ↦
      𝓕 (v15OdlyzkoTiltedSech a) y *
        𝓕 v15OdlyzkoH4Complex (w - y)) volume := by
  apply (v15OdlyzkoTiltedSech_fourier_integrable a ha₁ ha₂).mul_bdd
  · exact (v15OdlyzkoH4Fourier_continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards with y
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      v15OdlyzkoH4Complex (w - y)

/-- The explicit-formula transform of the complete `b = 4` kernel has
nonnegative real part at every weight in the open critical strip. -/
theorem v15OdlyzkoTiltedF4_fourier_re_nonneg (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) < a) (ha₂ : a < 1 / 2) :
    0 ≤ (𝓕 (v15OdlyzkoTiltedF4 a) w).re := by
  rw [v15OdlyzkoTiltedF4_fourier_eq_convolution a w ha₁ ha₂,
    MeasureTheory.convolution_mul]
  rw [← RCLike.re_eq_complex_re]
  rw [← integral_re (v15OdlyzkoTiltedF4_convolution_integrable a w ha₁ ha₂)]
  simp only [RCLike.re_eq_complex_re]
  apply integral_nonneg
  intro y
  change 0 ≤ (𝓕 (v15OdlyzkoTiltedSech a) y *
    𝓕 v15OdlyzkoH4Complex (w - y)).re
  rw [Complex.mul_re, v15OdlyzkoH4_fourier_im_eq_zero]
  simp only [mul_zero, sub_zero]
  exact mul_nonneg
    (v15OdlyzkoTiltedSech_fourier_re_pos a y ha₁ ha₂).le
    (v15OdlyzkoH4_fourier_re_nonneg (w - y))

private theorem v15OdlyzkoTiltedF4_fourier_eq_setIntegral (a w : ℝ) :
    𝓕 (v15OdlyzkoTiltedF4 a) w =
      ∫ x in Set.Icc (-8 : ℝ) 8,
        Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
          v15OdlyzkoTiltedF4 a x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    MeasurableSet.univ (Set.subset_univ _)
  intro x hx
  have hbound : 8 < |x| := by
    by_contra h
    apply hx.2
    change -8 ≤ x ∧ x ≤ 8
    rw [← abs_le]
    exact le_of_not_gt h
  simp [v15OdlyzkoTiltedF4,
    v15OdlyzkoF4_eq_zero_of_eight_lt_abs hbound]

/-- The explicit-formula transform varies continuously with its real
exponential weight.  Compact support provides one common integration set. -/
theorem v15OdlyzkoTiltedF4_fourier_continuous (w : ℝ) :
    Continuous (fun a : ℝ ↦ 𝓕 (v15OdlyzkoTiltedF4 a) w) := by
  have htilt : Continuous (fun p : ℝ × ℝ ↦
      v15OdlyzkoTiltedF4 p.1 p.2) := by
    unfold v15OdlyzkoTiltedF4
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_fst.mul continuous_snd)).mul
        (v15OdlyzkoF4_continuous.comp continuous_snd))
  have hphase : Continuous (fun p : ℝ × ℝ ↦
      Complex.exp ((↑(-2 * Real.pi * p.2 * w) : ℂ) * Complex.I)) := by
    fun_prop
  have hwhole : Continuous (fun p : ℝ × ℝ ↦
      Complex.exp ((↑(-2 * Real.pi * p.2 * w) : ℂ) * Complex.I) *
        v15OdlyzkoTiltedF4 p.1 p.2) := hphase.mul htilt
  have hset : Continuous (fun a : ℝ ↦
      ∫ x in Set.Icc (-8 : ℝ) 8,
        Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
          v15OdlyzkoTiltedF4 a x) :=
    continuous_parametric_integral_of_continuous hwhole isCompact_Icc
  convert hset using 1
  funext a
  exact v15OdlyzkoTiltedF4_fourier_eq_setIntegral a w

/-- The complete unconditional `b = 4` kernel has nonnegative explicit-formula
zero transform throughout the closed critical strip, including its boundary. -/
theorem v15OdlyzkoTiltedF4_fourier_re_nonneg_closed (a w : ℝ)
    (ha₁ : -(1 / 2 : ℝ) ≤ a) (ha₂ : a ≤ 1 / 2) :
    0 ≤ (𝓕 (v15OdlyzkoTiltedF4 a) w).re := by
  let S : Set ℝ := {b | 0 ≤ (𝓕 (v15OdlyzkoTiltedF4 b) w).re}
  have hS : IsClosed S :=
    isClosed_le continuous_const
      (Complex.continuous_re.comp (v15OdlyzkoTiltedF4_fourier_continuous w))
  have hsub : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ S := by
    intro b hb
    exact v15OdlyzkoTiltedF4_fourier_re_nonneg b w hb.1 hb.2
  have hclosure :
      closure (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) ⊆ S :=
    (hS.closure_subset_iff).2 hsub
  rw [closure_Ioo (by norm_num : -(1 / 2 : ℝ) ≠ 1 / 2)] at hclosure
  exact hclosure ⟨ha₁, ha₂⟩

/-- Odlyzko's transform `Phi(s)` in the normalization of equation (2.2) of
his 1990 survey. -/
def v15OdlyzkoPhi (s : ℂ) : ℂ :=
  ∫ x : ℝ, (v15OdlyzkoF4 x : ℂ) *
    Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))

/-- The source's complex parameter agrees exactly with Lean's real-frequency
Fourier convention after subtracting the center of the strip. -/
theorem v15OdlyzkoPhi_eq_fourier (s : ℂ) :
    v15OdlyzkoPhi s =
      𝓕 (v15OdlyzkoTiltedF4 (s.re - 1 / 2))
        (-s.im / (2 * Real.pi)) := by
  rw [v15OdlyzkoPhi, Real.fourier_real_eq_integral_exp_smul]
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
      ((-2 * Real.pi * x * (-s.im / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
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
  simp only [v15OdlyzkoTiltedF4, Complex.ofReal_mul]
  ring

/-- The source-exact zero transform has nonnegative real part for every
complex parameter in the closed critical strip. -/
theorem v15OdlyzkoPhi_re_nonneg_of_mem_closed_strip (s : ℂ)
    (hs₁ : 0 ≤ s.re) (hs₂ : s.re ≤ 1) :
    0 ≤ (v15OdlyzkoPhi s).re := by
  rw [v15OdlyzkoPhi_eq_fourier]
  apply v15OdlyzkoTiltedF4_fourier_re_nonneg_closed
  · linarith
  · linarith

/-- A summable family of source-normalized zero contributions has
nonnegative total real part when every parameter lies in the critical strip.
The explicit formula's existence and convergence statement is a separate
analytic-number-theory premise. -/
theorem v15OdlyzkoPhi_zero_tsum_re_nonneg {ι : Type*} (zeros : ι → ℂ)
    (hstrip : ∀ i, 0 ≤ (zeros i).re ∧ (zeros i).re ≤ 1)
    (hsum : Summable (fun i ↦ v15OdlyzkoPhi (zeros i))) :
    0 ≤ (∑' i, v15OdlyzkoPhi (zeros i)).re := by
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg fun i ↦
    v15OdlyzkoPhi_re_nonneg_of_mem_closed_strip (zeros i)
      (hstrip i).1 (hstrip i).2

end
end TraceEuclidean
