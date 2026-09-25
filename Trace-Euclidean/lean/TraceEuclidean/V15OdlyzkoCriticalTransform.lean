import DedekindZeta.DigammaIntegral
import TraceEuclidean.V15OdlyzkoFourthDecayCriterion
import TraceEuclidean.V15OdlyzkoZeroPairing
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Critical-line integrability of the Odlyzko transform

This module turns the proved fourth-power decay of the exact `b = 4` transform
into the integrability needed for the remaining Stark--Weil contour argument.
It also records that the transform is real on the critical line.
-/

namespace TraceEuclidean

noncomputable section

open Complex MeasureTheory FourierTransform
open scoped RealInnerProductSpace

/-- The exact Odlyzko transform is real on the critical line. -/
theorem v15OdlyzkoPhi_critical_im_eq_zero (t : ℝ) :
    (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hone : 1 - s = starRingEnd ℂ s := by
    dsimp [s]
    apply Complex.ext
    · norm_num
    · simp
  apply Complex.conj_eq_iff_im.mp
  calc
    starRingEnd ℂ (v15OdlyzkoPhi s) =
        v15OdlyzkoPhi (starRingEnd ℂ s) := by
      simpa using (v15OdlyzkoPhi_conj s).symm
    _ = v15OdlyzkoPhi (1 - s) := by rw [hone]
    _ = v15OdlyzkoPhi s := v15OdlyzkoPhi_one_sub s

/-- The fourth-power majorant used on the critical line is integrable. -/
theorem v15OdlyzkoCriticalMajorant_integrable (D : ℝ) :
    Integrable (fun t : ℝ ↦ D / (1 + |t|) ^ 4) volume := by
  have hbase :
      Integrable (fun t : ℝ ↦ D * (1 + ‖t‖) ^ (-(4 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (4 : ℝ)) (by norm_num)).const_mul D
  convert hbase using 1
  funext t
  rw [Real.norm_eq_abs, div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg (by positivity)]
  congr 1
  exact (Real.rpow_natCast (1 + |t|) 4).symm

/-- The quadratic-tail majorant needed after multiplying by `t²` is
integrable as well. -/
theorem v15OdlyzkoCriticalMajorant_two_integrable (D : ℝ) :
    Integrable (fun t : ℝ ↦ D / (1 + |t|) ^ 2) volume := by
  have hbase :
      Integrable (fun t : ℝ ↦ D * (1 + ‖t‖) ^ (-(2 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := (2 : ℝ)) (by norm_num)).const_mul D
  convert hbase using 1
  funext t
  rw [Real.norm_eq_abs, div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg (by positivity)]
  congr 1
  exact (Real.rpow_natCast (1 + |t|) 2).symm

/-- The exact Odlyzko transform is integrable along the critical line. -/
theorem v15OdlyzkoPhi_critical_integrable :
    Integrable
      (fun t : ℝ ↦ v15OdlyzkoPhi
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) volume := by
  obtain ⟨D, hD, hDecay⟩ := v15OdlyzkoPhi_exists_fourthPowerBound
  apply (v15OdlyzkoCriticalMajorant_integrable D).mono'
  · exact (v15OdlyzkoPhi_differentiable.continuous.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    have h := hDecay ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      (by norm_num) (by norm_num)
    simpa using h

/-- Fourth-power decay also gives an integrable quadratic moment on the
critical line. -/
theorem v15OdlyzkoPhi_critical_mul_sq_integrable :
    Integrable
      (fun t : ℝ ↦ ((t ^ 2 : ℝ) : ℂ) *
        v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) volume := by
  obtain ⟨D, hD, hDecay⟩ := v15OdlyzkoPhi_exists_fourthPowerBound
  apply (v15OdlyzkoCriticalMajorant_two_integrable D).mono'
  · exact ((by fun_prop : Continuous (fun t : ℝ ↦ ((t ^ 2 : ℝ) : ℂ))).mul
      (v15OdlyzkoPhi_differentiable.continuous.comp
        (by fun_prop : Continuous
          (fun t : ℝ ↦ (1 / 2 : ℂ) + (t : ℂ) * Complex.I)))).aestronglyMeasurable
  · filter_upwards with t
    let u : ℝ := 1 + |t|
    have hu : 0 < u := by dsimp [u]; positivity
    have ht : |t| ^ 2 ≤ u ^ 2 := by
      dsimp [u]
      nlinarith [abs_nonneg t]
    have hphi := hDecay ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      (by norm_num) (by norm_num)
    have hfirst :
        |t| ^ 2 *
            ‖v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          |t| ^ 2 * (D / u ^ 4) :=
      mul_le_mul_of_nonneg_left (by simpa [u] using hphi) (sq_nonneg |t|)
    have hsecond : |t| ^ 2 * (D / u ^ 4) ≤ D / u ^ 2 := by
      rw [show |t| ^ 2 * (D / u ^ 4) = (|t| ^ 2 * D) / u ^ 4 by ring]
      rw [div_le_div_iff₀ (pow_pos hu 4) (pow_pos hu 2)]
      nlinarith [mul_nonneg (mul_nonneg hD (sq_nonneg u))
        (sub_nonneg.mpr ht)]
    calc
      ‖((t ^ 2 : ℝ) : ℂ) *
          v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
          |t| ^ 2 *
            ‖v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
      _ ≤ |t| ^ 2 * (D / u ^ 4) := hfirst
      _ ≤ D / u ^ 2 := hsecond
      _ = D / (1 + |t|) ^ 2 := by rfl

/-- Rescaling the critical-line parameter gives exactly mathlib's Fourier
frequency normalization. -/
theorem v15OdlyzkoPhi_critical_scaled_eq_fourier (w : ℝ) :
    v15OdlyzkoPhi
        ((1 / 2 : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I) =
      𝓕 (v15OdlyzkoTiltedF4 0) w := by
  have h := v15OdlyzkoPhi_eq_fourier
    ((1 / 2 : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I)
  have hre :
      ((1 / 2 : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I).re -
          1 / 2 = 0 := by
    norm_num
  have hfreq :
      -((1 / 2 : ℂ) + (((-2 * Real.pi) * w : ℝ) : ℂ) * Complex.I).im /
          (2 * Real.pi) = w := by
    norm_num
  simpa only [hre, hfreq] using h

/-- The unscaled critical-line transform in mathlib's Fourier frequency. -/
theorem v15OdlyzkoPhi_critical_eq_fourier (t : ℝ) :
    v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      𝓕 (v15OdlyzkoTiltedF4 0) (-t / (2 * Real.pi)) := by
  have h := v15OdlyzkoPhi_eq_fourier
    ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)
  have hre :
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re - 1 / 2 = 0 := by
    norm_num
  have hfreq :
      -((1 / 2 : ℂ) + (t : ℂ) * Complex.I).im / (2 * Real.pi) =
        -t / (2 * Real.pi) := by
    norm_num
  simpa only [hre, hfreq] using h

/-- The Fourier transform of the central (`a = 0`) tilted kernel is integrable. -/
theorem v15OdlyzkoTiltedF4_zero_fourier_integrable :
    Integrable (𝓕 (v15OdlyzkoTiltedF4 0)) volume := by
  have hscaled := v15OdlyzkoPhi_critical_integrable.comp_mul_left'
    (show (-2 * Real.pi : ℝ) ≠ 0 by positivity)
  exact hscaled.congr (Filter.Eventually.of_forall fun w ↦
    v15OdlyzkoPhi_critical_scaled_eq_fourier w)

/-- Fourier inversion is therefore available pointwise for the exact central
Odlyzko kernel. -/
theorem v15OdlyzkoTiltedF4_zero_fourierInv_fourier (x : ℝ) :
    𝓕⁻ (𝓕 (v15OdlyzkoTiltedF4 0)) x = v15OdlyzkoTiltedF4 0 x := by
  exact congrFun
    ((v15OdlyzkoTiltedF4_continuous 0).fourierInv_fourier_eq
      (v15OdlyzkoTiltedF4_integrable 0)
      v15OdlyzkoTiltedF4_zero_fourier_integrable) x

/-- Fourier inversion written as an ordinary complex integral. -/
theorem v15OdlyzkoTiltedF4_zero_fourier_inversion_integral (x : ℝ) :
    (∫ w : ℝ,
        Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
          𝓕 (v15OdlyzkoTiltedF4 0) w) =
      v15OdlyzkoTiltedF4 0 x := by
  have h := v15OdlyzkoTiltedF4_zero_fourierInv_fourier x
  rw [Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul, RCLike.inner_apply, conj_trivial, mul_assoc,
    mul_comm, mul_left_comm] using h

/-- Fourier inversion after returning from mathlib frequency `w` to the
source's critical-line height `t`. -/
theorem v15OdlyzkoPhi_critical_inversion_integral (x : ℝ) :
    (∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      ((2 * Real.pi * v15OdlyzkoF4 x : ℝ) : ℂ) := by
  let a : ℝ := -1 / (2 * Real.pi)
  let g : ℝ → ℂ := fun w ↦
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 (v15OdlyzkoTiltedF4 0) w
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hpoint (t : ℝ) :
      Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        g (a * t) := by
    have hat : a * t = -t / (2 * Real.pi) := by
      dsimp [a]
      field_simp [Real.pi_ne_zero]
    dsimp [g]
    rw [hat, ← v15OdlyzkoPhi_critical_eq_fourier t]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  have habs : |a⁻¹| = 2 * Real.pi := by
    dsimp [a]
    rw [inv_div]
    rw [show (2 * Real.pi : ℝ) / (-1) = -(2 * Real.pi) by ring,
      abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    (∫ t : ℝ,
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ t : ℝ, g (a * t) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ = |a⁻¹| • ∫ w : ℝ, g w := Measure.integral_comp_mul_left g a
    _ = ((2 * Real.pi * v15OdlyzkoF4 x : ℝ) : ℂ) := by
      rw [habs]
      change (2 * Real.pi : ℝ) •
          (∫ w : ℝ,
            Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
              𝓕 (v15OdlyzkoTiltedF4 0) w) = _
      rw [v15OdlyzkoTiltedF4_zero_fourier_inversion_integral]
      simp [v15OdlyzkoTiltedF4]

/-- The phase-weighted critical-line transform remains integrable. -/
theorem v15OdlyzkoPhi_critical_phase_integrable (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) volume := by
  have hprod : Integrable
      (fun t : ℝ ↦
        v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I)) volume := by
    apply v15OdlyzkoPhi_critical_integrable.mul_bdd (c := 1)
    · exact (by fun_prop : Continuous
        (fun t : ℝ ↦ Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
    · filter_upwards with t
      rw [Complex.norm_exp]
      norm_num
  exact hprod.congr (Filter.Eventually.of_forall fun t ↦ by ring)

/-- The real cosine inversion formula in the source's critical-line
normalization. -/
theorem v15OdlyzkoPhi_critical_cosine_inversion (x : ℝ) :
    (∫ t : ℝ,
        (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re *
          Real.cos (t * x)) =
      2 * Real.pi * v15OdlyzkoF4 x := by
  have h := congrArg Complex.re (v15OdlyzkoPhi_critical_inversion_integral x)
  have hre := integral_re (v15OdlyzkoPhi_critical_phase_integrable x)
  have hreal :
      (∫ t : ℝ,
        (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) =
        (2 * Real.pi * v15OdlyzkoF4 x : ℝ) := by
    exact hre.trans (by simpa using h)
  calc
    (∫ t : ℝ,
        (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re *
          Real.cos (t * x)) =
        ∫ t : ℝ,
          (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
            v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Complex.mul_re, v15OdlyzkoPhi_critical_im_eq_zero]
      simp only [mul_zero, sub_zero, Complex.exp_re]
      simp [Real.cos_neg]
      ring
    _ = 2 * Real.pi * v15OdlyzkoF4 x := hreal

/-- The real critical-line transform is integrable. -/
theorem v15OdlyzkoPhi_critical_re_integrable :
    Integrable
      (fun t : ℝ ↦
        (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) volume :=
  Complex.reCLM.integrable_comp v15OdlyzkoPhi_critical_integrable

/-- The total mass of the real critical-line transform is `2π`, since the
source kernel is normalized by `F(0) = 1`. -/
theorem v15OdlyzkoPhi_critical_re_integral :
    (∫ t : ℝ,
      (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) =
        2 * Real.pi := by
  simpa using v15OdlyzkoPhi_critical_cosine_inversion 0

/-- The half-frequency cosine pairing used at real archimedean places. -/
theorem v15OdlyzkoPhi_critical_cosine_half_inversion (x : ℝ) :
    (∫ t : ℝ,
        (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re *
          Real.cos ((t / 2) * x)) =
      2 * Real.pi * v15OdlyzkoF4 (x / 2) := by
  calc
    (∫ t : ℝ,
        (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re *
          Real.cos ((t / 2) * x)) =
        ∫ t : ℝ,
          (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re *
            Real.cos (t * (x / 2)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [show (t / 2) * x = t * (x / 2) by ring]
    _ = 2 * Real.pi * v15OdlyzkoF4 (x / 2) :=
      v15OdlyzkoPhi_critical_cosine_inversion (x / 2)

end

end TraceEuclidean
