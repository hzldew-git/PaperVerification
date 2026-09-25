import TraceEuclidean.V15OdlyzkoCriticalTransform
import TraceEuclidean.V15OdlyzkoExplicitFormulaReduction
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Archimedean transform bridge for the Odlyzko formula

This file connects the proved Gauss integral for the critical-line digamma
terms with the two hyperbolic integrals in the source normalization.  The
first stage records the elementary improper integrals and pointwise kernel
identities needed after Fourier inversion.  The remaining stage justifies
the corresponding Fubini interchange.
-/

namespace TraceEuclidean

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- The Fermi--Dirac kernel is integrable on the positive half-line. -/
theorem v15OdlyzkoLogistic_integrableOn :
    IntegrableOn (fun x : ℝ ↦ 1 / (Real.exp x + 1)) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
  · exact (continuous_const.div
      (Real.continuous_exp.add continuous_const)
      (fun x ↦ (add_pos (Real.exp_pos x) zero_lt_one).ne')).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ (add_pos (Real.exp_pos x) zero_lt_one)
      (Real.exp_pos x)).2 (by linarith)

/-- The elementary logarithmic constant occurring in the complex-place
Gauss kernel. -/
theorem v15OdlyzkoLogistic_integral :
    (∫ x in Ioi (0 : ℝ), 1 / (Real.exp x + 1)) = Real.log 2 := by
  let F : ℝ → ℝ := fun x ↦ -Real.log (1 + Real.exp (-x))
  have hderiv (x : ℝ) : HasDerivAt F (1 / (Real.exp x + 1)) x := by
    have hinner : HasDerivAt (fun y : ℝ ↦ 1 + Real.exp (-y))
        (-Real.exp (-x)) x := by
      simpa [add_comm] using
        (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_add 1)
    have hlog := (hinner.log (by positivity)).const_sub (0 : ℝ)
    have hlog' : HasDerivAt F
        (0 - (-Real.exp (-x) / (1 + Real.exp (-x)))) x := by
      simpa [F] using hlog
    apply hlog'.congr_deriv
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have harg : Tendsto (fun x : ℝ ↦ 1 + Real.exp (-x)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
    have hlog : Tendsto (fun x : ℝ ↦ Real.log (1 + Real.exp (-x))) atTop
        (𝓝 (Real.log 1)) := (Real.continuousAt_log one_ne_zero).tendsto.comp harg
    simpa [F] using hlog.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ ↦ hderiv x) v15OdlyzkoLogistic_integrableOn hlim]
  norm_num [F]

/-- The arctangent kernel is integrable on the positive half-line. -/
theorem v15OdlyzkoArctanKernel_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ Real.exp x / (Real.exp (2 * x) + 1)) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
  · exact (Real.continuous_exp.div
      (Real.continuous_exp.comp (continuous_const.mul continuous_id) |>.add continuous_const)
      (fun x ↦ (add_pos (Real.exp_pos (2 * x)) zero_lt_one).ne')).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have heq : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.exp_neg, heq]
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀
      (add_pos (mul_pos (Real.exp_pos x) (Real.exp_pos x)) zero_lt_one)
      (Real.exp_pos x)).2 (by
      nlinarith [Real.exp_pos x])

/-- The elementary arctangent constant occurring in the real-place kernel. -/
theorem v15OdlyzkoArctanKernel_integral :
    (∫ x in Ioi (0 : ℝ),
      Real.exp x / (Real.exp (2 * x) + 1)) = Real.pi / 4 := by
  let F : ℝ → ℝ := Real.arctan ∘ Real.exp
  have hderiv (x : ℝ) :
      HasDerivAt F (Real.exp x / (Real.exp (2 * x) + 1)) x := by
    have h := (Real.hasDerivAt_arctan' (Real.exp x)).comp x (Real.hasDerivAt_exp x)
    have h' : HasDerivAt F ((1 + Real.exp x ^ 2)⁻¹ * Real.exp x) x := by
      simpa [F] using h
    apply h'.congr_deriv
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    ring
  have hlim : Tendsto F atTop (𝓝 (Real.pi / 2)) := by
    exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      Real.tendsto_exp_atTop
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ ↦ hderiv x) v15OdlyzkoArctanKernel_integrableOn hlim]
  simp [F, Real.arctan_one]
  ring

/-- The half-speed logistic kernel has integral `2 log 2`. -/
theorem v15OdlyzkoLogistic_half_integral :
    (∫ x in Ioi (0 : ℝ), 1 / (Real.exp (x / 2) + 1)) =
      2 * Real.log 2 := by
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ ↦ 1 / (Real.exp x + 1)) 0 (by norm_num : (0 : ℝ) < 1 / 2)
  have h' :
      (∫ x in Ioi (0 : ℝ), 1 / (Real.exp ((1 / 2 : ℝ) * x) + 1)) =
        (1 / 2 : ℝ)⁻¹ • ∫ x in Ioi (0 : ℝ), 1 / (Real.exp x + 1) := by
    simpa only [mul_zero] using h
  calc
    (∫ x in Ioi (0 : ℝ), 1 / (Real.exp (x / 2) + 1)) =
        ∫ x in Ioi (0 : ℝ), 1 / (Real.exp ((1 / 2 : ℝ) * x) + 1) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change 1 / (Real.exp (x / 2) + 1) =
            1 / (Real.exp ((1 / 2 : ℝ) * x) + 1)
          rw [show x / 2 = (1 / 2 : ℝ) * x by ring]
    _ = (1 / 2 : ℝ)⁻¹ • ∫ x in Ioi (0 : ℝ),
        1 / (Real.exp x + 1) := h'
    _ = 2 * Real.log 2 := by
      rw [v15OdlyzkoLogistic_integral]
      norm_num [smul_eq_mul]

/-- The half-speed arctangent kernel has integral `π/2`. -/
theorem v15OdlyzkoArctanKernel_half_integral :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (x / 2) / (Real.exp x + 1)) = Real.pi / 2 := by
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ ↦ Real.exp x / (Real.exp (2 * x) + 1)) 0
      (by norm_num : (0 : ℝ) < 1 / 2)
  have h' :
      (∫ x in Ioi (0 : ℝ),
          Real.exp ((1 / 2 : ℝ) * x) /
            (Real.exp (2 * ((1 / 2 : ℝ) * x)) + 1)) =
        (1 / 2 : ℝ)⁻¹ • ∫ x in Ioi (0 : ℝ),
          Real.exp x / (Real.exp (2 * x) + 1) := by
    simpa only [mul_zero] using h
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (x / 2) / (Real.exp x + 1)) =
        ∫ x in Ioi (0 : ℝ),
          Real.exp ((1 / 2 : ℝ) * x) /
            (Real.exp (2 * ((1 / 2 : ℝ) * x)) + 1) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change Real.exp (x / 2) / (Real.exp x + 1) =
            Real.exp ((1 / 2 : ℝ) * x) /
              (Real.exp (2 * ((1 / 2 : ℝ) * x)) + 1)
          ring_nf
    _ = (1 / 2 : ℝ)⁻¹ • ∫ x in Ioi (0 : ℝ),
        Real.exp x / (Real.exp (2 * x) + 1) := h'
    _ = Real.pi / 2 := by
      rw [v15OdlyzkoArctanKernel_integral]
      norm_num [smul_eq_mul]
      ring

/-- Integrability of the half-speed logistic kernel. -/
theorem v15OdlyzkoLogistic_half_integrableOn :
    IntegrableOn (fun x : ℝ ↦ 1 / (Real.exp (x / 2) + 1)) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ ↦ 1 / (Real.exp x + 1)) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).2
    (by simpa using v15OdlyzkoLogistic_integrableOn)
  exact h.congr_fun (fun x _ ↦ by
    rw [show x / 2 = (1 / 2 : ℝ) * x by ring]) measurableSet_Ioi

/-- Integrability of the half-speed arctangent kernel. -/
theorem v15OdlyzkoArctanKernel_half_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ Real.exp (x / 2) / (Real.exp x + 1)) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ ↦ Real.exp x / (Real.exp (2 * x) + 1)) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).2
    (by simpa using v15OdlyzkoArctanKernel_integrableOn)
  exact h.congr_fun (fun x _ ↦ by
    change Real.exp ((1 / 2 : ℝ) * x) /
        (Real.exp (2 * ((1 / 2 : ℝ) * x)) + 1) =
      Real.exp (x / 2) / (Real.exp x + 1)
    ring_nf) measurableSet_Ioi

/-- Polynomial times exponential decay is integrable on the positive
half-line.  This form is convenient for the quadratic Fubini majorant. -/
theorem v15OdlyzkoPowMulExpNeg_integrableOn (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ k * Real.exp (-(a * x))) (Ioi 0) := by
  have hkey := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := a) (by positivity) ha
  have hne :
      (∫ x in Ioi (0 : ℝ),
        x ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * x))) ≠ 0 := by
    rw [hkey]
    positivity
  have hint : IntegrableOn
      (fun x : ℝ ↦
        x ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * x))) (Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  exact hint.congr_fun (fun x _ ↦ by
    change x ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * x)) =
      x ^ k * Real.exp (-(a * x))
    rw [show ((k : ℝ) + 1) - 1 = (k : ℝ) by ring,
      Real.rpow_natCast]) measurableSet_Ioi

/-- A global lower bound for the removable denominator in Gauss' kernel. -/
theorem v15Odlyzko_div_one_add_le_one_sub_exp_neg {x : ℝ} (hx : 0 < x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hlin : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) hlin
  have hxone : 1 + x ≠ 0 := by linarith
  calc
    x / (1 + x) = 1 - 1 / (1 + x) := by
      field_simp [hxone]
      ring
    _ ≤ 1 - Real.exp (-x) := by linarith

/-- Reciprocal form of the global Gauss-denominator bound. -/
theorem v15Odlyzko_one_div_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) :
    1 / (1 - Real.exp (-x)) ≤ (1 + x) / x := by
  have hbase := v15Odlyzko_div_one_add_le_one_sub_exp_neg hx
  calc
    1 / (1 - Real.exp (-x)) ≤ 1 / (x / (1 + x)) :=
      one_div_le_one_div_of_le (by positivity) hbase
    _ = (1 + x) / x := by
      field_simp [hx.ne']

/-- The quadratic majorant controlling the cancellation in Gauss' kernel is
integrable for every positive vertical-line parameter. -/
theorem v15OdlyzkoDigammaQuadraticKernel_integrableOn {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ ↦
        Real.exp (-(a * x)) * x ^ 2 / (1 - Real.exp (-x))) (Ioi 0) := by
  have hmajor : IntegrableOn
      (fun x : ℝ ↦
        x * Real.exp (-(a * x)) + x ^ 2 * Real.exp (-(a * x))) (Ioi 0) :=
    by
      have hsum := (v15OdlyzkoPowMulExpNeg_integrableOn 1 ha).add
        (v15OdlyzkoPowMulExpNeg_integrableOn 2 ha)
      exact hsum.congr_fun (fun x _ ↦ by simp [pow_one]) measurableSet_Ioi
  apply hmajor.mono'
  · have hcont : ContinuousOn
        (fun x : ℝ ↦
          Real.exp (-(a * x)) * x ^ 2 / (1 - Real.exp (-x))) (Ioi 0) := by
      intro x hx
      have hden : 1 - Real.exp (-x) ≠ 0 := by
        have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
        linarith
      exact ((by fun_prop : ContinuousAt
        (fun y : ℝ ↦ Real.exp (-(a * y)) * y ^ 2) x).div
          (by fun_prop : ContinuousAt (fun y : ℝ ↦ 1 - Real.exp (-y)) x)
          hden).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hdenpos : 0 < 1 - Real.exp (-x) := by
      have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hxpos)
      linarith
    have hnonneg :
        0 ≤ Real.exp (-(a * x)) * x ^ 2 / (1 - Real.exp (-x)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hrecip := v15Odlyzko_one_div_one_sub_exp_neg_le hx
    rw [div_eq_mul_inv]
    calc
      Real.exp (-(a * x)) * x ^ 2 * (1 - Real.exp (-x))⁻¹ ≤
          Real.exp (-(a * x)) * x ^ 2 * ((1 + x) / x) := by
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hrecip)
          (by positivity)
      _ = x * Real.exp (-(a * x)) +
          x ^ 2 * Real.exp (-(a * x)) := by
        field_simp [hxpos.ne']

/-- The real part of the critical transform retains its integrable quadratic
moment. -/
theorem v15OdlyzkoPhi_critical_re_mul_sq_integrable :
    Integrable
      (fun t : ℝ ↦ t ^ 2 *
        (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) volume := by
  have h := Complex.reCLM.integrable_comp
    v15OdlyzkoPhi_critical_mul_sq_integrable
  exact h.congr (Filter.Eventually.of_forall fun t ↦ by
    change ((((t ^ 2 : ℝ) : ℂ) *
      v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring)

/-- The real critical-line transform, isolated as a real-valued function for
the archimedean Fubini argument. -/
def v15OdlyzkoCriticalReal (t : ℝ) : ℝ :=
  (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re

@[fun_prop]
theorem v15OdlyzkoCriticalReal_continuous :
    Continuous v15OdlyzkoCriticalReal := by
  exact Complex.continuous_re.comp
    (v15OdlyzkoPhi_differentiable.continuous.comp (by fun_prop))

@[fun_prop]
theorem v15OdlyzkoCriticalReal_measurable :
    Measurable v15OdlyzkoCriticalReal :=
  v15OdlyzkoCriticalReal_continuous.measurable

/-- Gauss' real digamma kernel in the normalization used below. -/
def v15OdlyzkoDigammaKernel (a t x : ℝ) : ℝ :=
  (Real.exp (-x) - Real.exp (-(a * x)) * Real.cos (t * x)) /
    (1 - Real.exp (-x))

@[fun_prop]
theorem v15OdlyzkoDigammaKernel_measurable (a : ℝ) :
    Measurable (fun z : ℝ × ℝ ↦
      v15OdlyzkoDigammaKernel a z.1 z.2) := by
  unfold v15OdlyzkoDigammaKernel
  fun_prop

/-- The oscillatory remainder after subtracting the zero-frequency Gauss
kernel. -/
def v15OdlyzkoDigammaRemainder (a t x : ℝ) : ℝ :=
  Real.exp (-(a * x)) * (1 - Real.cos (t * x)) /
    (1 - Real.exp (-x))

@[fun_prop]
theorem v15OdlyzkoDigammaRemainder_measurable (a : ℝ) :
    Measurable (fun z : ℝ × ℝ ↦
      v15OdlyzkoDigammaRemainder a z.1 z.2) := by
  unfold v15OdlyzkoDigammaRemainder
  fun_prop

/-- Splitting at zero frequency exposes the quadratic cancellation at the
origin. -/
theorem v15OdlyzkoDigammaKernel_eq_zero_add_remainder
    (a t : ℝ) {x : ℝ} (hx : 0 < x) :
    v15OdlyzkoDigammaKernel a t x =
      v15OdlyzkoDigammaKernel a 0 x +
        v15OdlyzkoDigammaRemainder a t x := by
  have hden : 1 - Real.exp (-x) ≠ 0 := by
    have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
    linarith
  unfold v15OdlyzkoDigammaKernel v15OdlyzkoDigammaRemainder
  simp only [zero_mul, Real.cos_zero, mul_one]
  field_simp [hden]
  ring

/-- The oscillatory remainder is bounded by the separated quadratic
majorant used in the product-integrability proof. -/
theorem v15OdlyzkoDigammaRemainder_norm_le
    (a u t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖v15OdlyzkoCriticalReal u *
        v15OdlyzkoDigammaRemainder a t x‖ ≤
      ‖t ^ 2 * v15OdlyzkoCriticalReal u‖ *
        ((1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x)))) := by
  have hdenpos : 0 < 1 - Real.exp (-x) := by
    have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
    linarith
  have hcos0 : 0 ≤ 1 - Real.cos (t * x) := by
    linarith [Real.cos_le_one (t * x)]
  have hcos2 : 1 - Real.cos (t * x) ≤ (t * x) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t * x)]
  have hrem0 : 0 ≤ v15OdlyzkoDigammaRemainder a t x := by
    unfold v15OdlyzkoDigammaRemainder
    positivity
  have hquad0 :
      0 ≤ (1 / 2 : ℝ) *
        (Real.exp (-(a * x)) * x ^ 2 /
          (1 - Real.exp (-x))) := by positivity
  have hremle :
      v15OdlyzkoDigammaRemainder a t x ≤
        t ^ 2 * ((1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x)))) := by
    unfold v15OdlyzkoDigammaRemainder
    rw [div_le_iff₀ hdenpos]
    calc
      Real.exp (-(a * x)) * (1 - Real.cos (t * x)) ≤
          Real.exp (-(a * x)) * ((t * x) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcos2 (Real.exp_pos _).le
      _ = t ^ 2 *
          ((1 / 2 : ℝ) *
            (Real.exp (-(a * x)) * x ^ 2 /
              (1 - Real.exp (-x)))) *
            (1 - Real.exp (-x)) := by
        field_simp [hdenpos.ne']
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrem0,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
  calc
    |v15OdlyzkoCriticalReal u| * v15OdlyzkoDigammaRemainder a t x ≤
        |v15OdlyzkoCriticalReal u| *
          (t ^ 2 * ((1 / 2 : ℝ) *
            (Real.exp (-(a * x)) * x ^ 2 /
              (1 - Real.exp (-x))))) :=
      mul_le_mul_of_nonneg_left hremle (abs_nonneg _)
    _ = t ^ 2 * |v15OdlyzkoCriticalReal u| *
        ((1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x)))) := by ring

/-- Integrability of the real critical-line transform in the abbreviated
notation used by this file. -/
theorem v15OdlyzkoCriticalReal_integrable :
    Integrable v15OdlyzkoCriticalReal volume := by
  change Integrable
    (fun t : ℝ ↦
      (v15OdlyzkoPhi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) volume
  exact v15OdlyzkoPhi_critical_re_integrable

/-- Integrability of the quadratic moment in the abbreviated notation. -/
theorem v15OdlyzkoCriticalReal_mul_sq_integrable :
    Integrable
      (fun t : ℝ ↦ t ^ 2 * v15OdlyzkoCriticalReal t) volume := by
  simpa [v15OdlyzkoCriticalReal] using
    v15OdlyzkoPhi_critical_re_mul_sq_integrable

/-- The critical-line transform times the oscillatory Gauss remainder is
absolutely integrable on the relevant product space. -/
theorem v15OdlyzkoCritical_mul_digammaRemainder_integrable
    {a : ℝ} (ha0 : 0 < a) :
    Integrable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaRemainder a z.1 z.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hquadratic : Integrable
      (fun x : ℝ ↦
        (1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x))))
      (volume.restrict (Ioi 0)) :=
    (v15OdlyzkoDigammaQuadraticKernel_integrableOn ha0).const_mul (1 / 2)
  have hmajor : Integrable
      (fun z : ℝ × ℝ ↦
        (z.1 ^ 2 * v15OdlyzkoCriticalReal z.1) *
          ((1 / 2 : ℝ) *
            (Real.exp (-(a * z.2)) * z.2 ^ 2 /
              (1 - Real.exp (-z.2)))))
      (volume.prod (volume.restrict (Ioi 0))) :=
    v15OdlyzkoCriticalReal_mul_sq_integrable.mul_prod hquadratic
  apply hmajor.mono
  · exact ((v15OdlyzkoCriticalReal_measurable.comp measurable_fst).mul
      (v15OdlyzkoDigammaRemainder_measurable a)).aestronglyMeasurable
  · filter_upwards [
      (Measure.quasiMeasurePreserving_snd
        (μ := volume) (ν := volume.restrict (Ioi 0))).ae
          (ae_restrict_mem measurableSet_Ioi)] with z hz
    let t := z.1
    let x := z.2
    have hx : 0 < x := hz
    calc
      ‖v15OdlyzkoCriticalReal t *
          v15OdlyzkoDigammaRemainder a t x‖ ≤
          ‖t ^ 2 * v15OdlyzkoCriticalReal t‖ *
            ((1 / 2 : ℝ) *
              (Real.exp (-(a * x)) * x ^ 2 /
                (1 - Real.exp (-x)))) :=
        v15OdlyzkoDigammaRemainder_norm_le a t t hx
      _ = ‖(t ^ 2 * v15OdlyzkoCriticalReal t) *
            ((1 / 2 : ℝ) *
              (Real.exp (-(a * x)) * x ^ 2 /
                (1 - Real.exp (-x))))‖ := by
        have hdenpos : 0 < 1 - Real.exp (-x) := by
          have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
          linarith
        have hquad0 : 0 ≤ (1 / 2 : ℝ) *
            (Real.exp (-(a * x)) * x ^ 2 /
              (1 - Real.exp (-x))) := by positivity
        simp only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg t), abs_of_nonneg hquad0]

/-- The critical-line transform multiplied by Gauss' full kernel is
absolutely integrable on the product of the spectral line and the positive
half-line. -/
theorem v15OdlyzkoCritical_mul_digammaKernel_integrable
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Integrable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaKernel a z.1 z.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hzero : IntegrableOn
      (fun x : ℝ ↦ v15OdlyzkoDigammaKernel a 0 x) (Ioi 0) := by
    simpa [v15OdlyzkoDigammaKernel] using
      DedekindZeta.DigammaIntegral.digammaGaussKernel_integrableOn
        ha0 ha1 0
  have hzeroProd : Integrable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaKernel a 0 z.2)
      (volume.prod (volume.restrict (Ioi 0))) :=
    v15OdlyzkoCriticalReal_integrable.mul_prod hzero
  have hsum := hzeroProd.add
    (v15OdlyzkoCritical_mul_digammaRemainder_integrable ha0)
  apply hsum.congr
  filter_upwards [
    (Measure.quasiMeasurePreserving_snd
      (μ := volume) (ν := volume.restrict (Ioi 0))).ae
        (ae_restrict_mem measurableSet_Ioi)] with z hz
  change v15OdlyzkoCriticalReal z.1 *
      v15OdlyzkoDigammaKernel a 0 z.2 +
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaRemainder a z.1 z.2 =
    v15OdlyzkoCriticalReal z.1 *
      v15OdlyzkoDigammaKernel a z.1 z.2
  rw [v15OdlyzkoDigammaKernel_eq_zero_add_remainder a z.1 hz]
  ring

/-- Fourier inversion evaluates the spectral integral of Gauss' kernel at
each fixed positive-half-line variable. -/
theorem v15OdlyzkoCritical_mul_digammaKernel_inner_integral
    (a x : ℝ) :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        v15OdlyzkoDigammaKernel a t x) =
      2 * Real.pi *
        ((Real.exp (-x) - Real.exp (-(a * x)) * v15OdlyzkoF4 x) /
          (1 - Real.exp (-x))) := by
  have hcos : Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t * Real.cos (t * x)) volume := by
    apply v15OdlyzkoCriticalReal_integrable.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)
  have hfirst : Integrable
      (fun t : ℝ ↦
        (Real.exp (-x) / (1 - Real.exp (-x))) *
          v15OdlyzkoCriticalReal t) volume :=
    v15OdlyzkoCriticalReal_integrable.const_mul _
  have hsecond : Integrable
      (fun t : ℝ ↦
        (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
          (v15OdlyzkoCriticalReal t * Real.cos (t * x))) volume :=
    hcos.const_mul _
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        v15OdlyzkoDigammaKernel a t x) =
        ∫ t : ℝ,
          (Real.exp (-x) / (1 - Real.exp (-x))) *
              v15OdlyzkoCriticalReal t -
            (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
              (v15OdlyzkoCriticalReal t * Real.cos (t * x)) := by
      apply integral_congr_ae
      filter_upwards with t
      unfold v15OdlyzkoDigammaKernel
      ring
    _ = (Real.exp (-x) / (1 - Real.exp (-x))) *
          (∫ t : ℝ, v15OdlyzkoCriticalReal t) -
        (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
          (∫ t : ℝ,
            v15OdlyzkoCriticalReal t * Real.cos (t * x)) := by
      rw [integral_sub hfirst hsecond, integral_const_mul,
        integral_const_mul]
    _ = 2 * Real.pi *
        ((Real.exp (-x) - Real.exp (-(a * x)) * v15OdlyzkoF4 x) /
          (1 - Real.exp (-x))) := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        show (∫ t : ℝ,
            v15OdlyzkoCriticalReal t * Real.cos (t * x)) =
              2 * Real.pi * v15OdlyzkoF4 x by
          simpa [v15OdlyzkoCriticalReal] using
            v15OdlyzkoPhi_critical_cosine_inversion x]
      ring

/-- Absolute product integrability and Fourier inversion justify the full
Fubini interchange for Gauss' kernel. -/
theorem v15OdlyzkoCritical_mul_digammaKernel_fubini
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∫ t : ℝ,
      ∫ x in Ioi (0 : ℝ),
        v15OdlyzkoCriticalReal t *
          v15OdlyzkoDigammaKernel a t x) =
      2 * Real.pi *
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-(a * x)) * v15OdlyzkoF4 x) /
            (1 - Real.exp (-x)) := by
  have hjoint := v15OdlyzkoCritical_mul_digammaKernel_integrable ha0 ha1
  calc
    (∫ t : ℝ,
      ∫ x in Ioi (0 : ℝ),
        v15OdlyzkoCriticalReal t *
          v15OdlyzkoDigammaKernel a t x) =
        ∫ x in Ioi (0 : ℝ),
          ∫ t : ℝ,
            v15OdlyzkoCriticalReal t *
              v15OdlyzkoDigammaKernel a t x :=
      integral_integral_swap hjoint
    _ = ∫ x in Ioi (0 : ℝ),
        2 * Real.pi *
          ((Real.exp (-x) - Real.exp (-(a * x)) * v15OdlyzkoF4 x) /
            (1 - Real.exp (-x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact v15OdlyzkoCritical_mul_digammaKernel_inner_integral a x
    _ = 2 * Real.pi *
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) - Real.exp (-(a * x)) * v15OdlyzkoF4 x) /
            (1 - Real.exp (-x)) := by
      rw [integral_const_mul]

/-- A fixed rescaling of the spectral frequency preserves the integrable
quadratic moment. -/
theorem v15OdlyzkoCriticalReal_scaled_mul_sq_integrable (b : ℝ) :
    Integrable
      (fun t : ℝ ↦ (b * t) ^ 2 * v15OdlyzkoCriticalReal t) volume := by
  have h := v15OdlyzkoCriticalReal_mul_sq_integrable.const_mul (b ^ 2)
  exact h.congr (Filter.Eventually.of_forall fun t ↦ by ring)

/-- Product integrability for Gauss' kernel after a fixed rescaling of the
spectral frequency. -/
theorem v15OdlyzkoCritical_mul_digammaKernel_scaled_integrable
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (b : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaKernel a (b * z.1) z.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hzero : IntegrableOn
      (fun x : ℝ ↦ v15OdlyzkoDigammaKernel a 0 x) (Ioi 0) := by
    simpa [v15OdlyzkoDigammaKernel] using
      DedekindZeta.DigammaIntegral.digammaGaussKernel_integrableOn
        ha0 ha1 0
  have hzeroProd : Integrable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaKernel a 0 z.2)
      (volume.prod (volume.restrict (Ioi 0))) :=
    v15OdlyzkoCriticalReal_integrable.mul_prod hzero
  have hquadratic : Integrable
      (fun x : ℝ ↦
        (1 / 2 : ℝ) *
          (Real.exp (-(a * x)) * x ^ 2 /
            (1 - Real.exp (-x))))
      (volume.restrict (Ioi 0)) :=
    (v15OdlyzkoDigammaQuadraticKernel_integrableOn ha0).const_mul (1 / 2)
  have hmajor : Integrable
      (fun z : ℝ × ℝ ↦
        ((b * z.1) ^ 2 * v15OdlyzkoCriticalReal z.1) *
          ((1 / 2 : ℝ) *
            (Real.exp (-(a * z.2)) * z.2 ^ 2 /
              (1 - Real.exp (-z.2)))))
      (volume.prod (volume.restrict (Ioi 0))) :=
    (v15OdlyzkoCriticalReal_scaled_mul_sq_integrable b).mul_prod hquadratic
  have hremMeas : Measurable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoDigammaRemainder a (b * z.1) z.2) := by
    unfold v15OdlyzkoDigammaRemainder
    fun_prop
  have hremainder : Integrable
      (fun z : ℝ × ℝ ↦
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaRemainder a (b * z.1) z.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
    apply hmajor.mono
    · exact ((v15OdlyzkoCriticalReal_measurable.comp measurable_fst).mul
        hremMeas).aestronglyMeasurable
    · filter_upwards [
        (Measure.quasiMeasurePreserving_snd
          (μ := volume) (ν := volume.restrict (Ioi 0))).ae
            (ae_restrict_mem measurableSet_Ioi)] with z hz
      calc
        ‖v15OdlyzkoCriticalReal z.1 *
            v15OdlyzkoDigammaRemainder a (b * z.1) z.2‖ ≤
            ‖(b * z.1) ^ 2 * v15OdlyzkoCriticalReal z.1‖ *
              ((1 / 2 : ℝ) *
                (Real.exp (-(a * z.2)) * z.2 ^ 2 /
                  (1 - Real.exp (-z.2)))) :=
          v15OdlyzkoDigammaRemainder_norm_le a z.1 (b * z.1) hz
        _ = ‖((b * z.1) ^ 2 * v15OdlyzkoCriticalReal z.1) *
              ((1 / 2 : ℝ) *
                (Real.exp (-(a * z.2)) * z.2 ^ 2 /
                  (1 - Real.exp (-z.2))))‖ := by
          have hdenpos : 0 < 1 - Real.exp (-z.2) := by
            have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
            linarith
          have hquad0 : 0 ≤ (1 / 2 : ℝ) *
              (Real.exp (-(a * z.2)) * z.2 ^ 2 /
                (1 - Real.exp (-z.2))) := by positivity
          simp only [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (sq_nonneg (b * z.1)), abs_of_nonneg hquad0]
  have hsum := hzeroProd.add hremainder
  apply hsum.congr
  filter_upwards [
    (Measure.quasiMeasurePreserving_snd
      (μ := volume) (ν := volume.restrict (Ioi 0))).ae
        (ae_restrict_mem measurableSet_Ioi)] with z hz
  change v15OdlyzkoCriticalReal z.1 *
      v15OdlyzkoDigammaKernel a 0 z.2 +
        v15OdlyzkoCriticalReal z.1 *
          v15OdlyzkoDigammaRemainder a (b * z.1) z.2 =
    v15OdlyzkoCriticalReal z.1 *
      v15OdlyzkoDigammaKernel a (b * z.1) z.2
  rw [v15OdlyzkoDigammaKernel_eq_zero_add_remainder a (b * z.1) hz]
  ring

/-- Fourier inversion for Gauss' kernel with a fixed spectral rescaling. -/
theorem v15OdlyzkoCritical_mul_digammaKernel_scaled_inner_integral
    (a b x : ℝ) :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        v15OdlyzkoDigammaKernel a (b * t) x) =
      2 * Real.pi *
        ((Real.exp (-x) -
            Real.exp (-(a * x)) * v15OdlyzkoF4 (b * x)) /
          (1 - Real.exp (-x))) := by
  have hcos : Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t * Real.cos ((b * t) * x)) volume := by
    apply v15OdlyzkoCriticalReal_integrable.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one ((b * t) * x)
  have hcosIntegral :
      (∫ t : ℝ,
        v15OdlyzkoCriticalReal t * Real.cos ((b * t) * x)) =
        2 * Real.pi * v15OdlyzkoF4 (b * x) := by
    calc
      (∫ t : ℝ,
        v15OdlyzkoCriticalReal t * Real.cos ((b * t) * x)) =
          ∫ t : ℝ,
            v15OdlyzkoCriticalReal t * Real.cos (t * (b * x)) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [show (b * t) * x = t * (b * x) by ring]
      _ = 2 * Real.pi * v15OdlyzkoF4 (b * x) := by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_cosine_inversion (b * x)
  have hfirst : Integrable
      (fun t : ℝ ↦
        (Real.exp (-x) / (1 - Real.exp (-x))) *
          v15OdlyzkoCriticalReal t) volume :=
    v15OdlyzkoCriticalReal_integrable.const_mul _
  have hsecond : Integrable
      (fun t : ℝ ↦
        (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
          (v15OdlyzkoCriticalReal t * Real.cos ((b * t) * x))) volume :=
    hcos.const_mul _
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        v15OdlyzkoDigammaKernel a (b * t) x) =
        ∫ t : ℝ,
          (Real.exp (-x) / (1 - Real.exp (-x))) *
              v15OdlyzkoCriticalReal t -
            (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
              (v15OdlyzkoCriticalReal t * Real.cos ((b * t) * x)) := by
      apply integral_congr_ae
      filter_upwards with t
      unfold v15OdlyzkoDigammaKernel
      ring
    _ = (Real.exp (-x) / (1 - Real.exp (-x))) *
          (∫ t : ℝ, v15OdlyzkoCriticalReal t) -
        (Real.exp (-(a * x)) / (1 - Real.exp (-x))) *
          (∫ t : ℝ,
            v15OdlyzkoCriticalReal t * Real.cos ((b * t) * x)) := by
      rw [integral_sub hfirst hsecond, integral_const_mul,
        integral_const_mul]
    _ = 2 * Real.pi *
        ((Real.exp (-x) -
            Real.exp (-(a * x)) * v15OdlyzkoF4 (b * x)) /
          (1 - Real.exp (-x))) := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        hcosIntegral]
      ring

/-- Fubini's theorem for the spectrally rescaled Gauss kernel. -/
theorem v15OdlyzkoCritical_mul_digammaKernel_scaled_fubini
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (b : ℝ) :
    (∫ t : ℝ,
      ∫ x in Ioi (0 : ℝ),
        v15OdlyzkoCriticalReal t *
          v15OdlyzkoDigammaKernel a (b * t) x) =
      2 * Real.pi *
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) -
              Real.exp (-(a * x)) * v15OdlyzkoF4 (b * x)) /
            (1 - Real.exp (-x)) := by
  have hjoint := v15OdlyzkoCritical_mul_digammaKernel_scaled_integrable
    ha0 ha1 b
  calc
    (∫ t : ℝ,
      ∫ x in Ioi (0 : ℝ),
        v15OdlyzkoCriticalReal t *
          v15OdlyzkoDigammaKernel a (b * t) x) =
        ∫ x in Ioi (0 : ℝ),
          ∫ t : ℝ,
            v15OdlyzkoCriticalReal t *
              v15OdlyzkoDigammaKernel a (b * t) x :=
      integral_integral_swap hjoint
    _ = ∫ x in Ioi (0 : ℝ),
        2 * Real.pi *
          ((Real.exp (-x) -
              Real.exp (-(a * x)) * v15OdlyzkoF4 (b * x)) /
            (1 - Real.exp (-x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact v15OdlyzkoCritical_mul_digammaKernel_scaled_inner_integral a b x
    _ = 2 * Real.pi *
        ∫ x in Ioi (0 : ℝ),
          (Real.exp (-x) -
              Real.exp (-(a * x)) * v15OdlyzkoF4 (b * x)) /
            (1 - Real.exp (-x)) := by
      rw [integral_const_mul]

/-- The complex-place Gauss remainder is the source sinh kernel plus its
exact elementary constant. -/
theorem v15OdlyzkoComplexGaussKernel_eq (x : ℝ) (hx : 0 < x) :
    (Real.exp (-x) - Real.exp (-(1 / 2 : ℝ) * x) * v15OdlyzkoF4 x) /
        (1 - Real.exp (-x)) =
      (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) -
        1 / (Real.exp (x / 2) + 1) := by
  let q : ℝ := Real.exp (-(x / 2))
  have hq0 : q ≠ 0 := by dsimp [q]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqlt : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : 1 - q ^ 2 ≠ 0 := by nlinarith
  have hqadd : 1 + q ≠ 0 := by positivity
  have hnegHalf : Real.exp (-(1 / 2 : ℝ) * x) = q := by
    dsimp [q]
    congr 1
    ring
  have hneg : Real.exp (-x) = q ^ 2 := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hposHalf : Real.exp (x / 2) = q⁻¹ := by
    calc
      Real.exp (x / 2) = Real.exp (-(-(x / 2))) := by congr 1; ring
      _ = (Real.exp (-(x / 2)))⁻¹ := Real.exp_neg _
      _ = q⁻¹ := by rfl
  have hsinh : 2 * Real.sinh (x / 2) = (1 - q ^ 2) / q := by
    rw [Real.sinh_eq, hposHalf]
    change 2 * ((q⁻¹ - q) / 2) = _
    field_simp [hq0]
  have hlogistic : Real.exp (x / 2) + 1 = (1 + q) / q := by
    rw [hposHalf]
    field_simp [hq0]
  rw [hneg, hnegHalf, hsinh, hlogistic]
  field_simp [hq0, hq2, hqadd]
  ring

/-- The real-place Gauss remainder splits into the source sinh and cosh
kernels and an elementary remainder. -/
theorem v15OdlyzkoRealGaussKernel_eq (x : ℝ) (hx : 0 < x) :
    2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
        v15OdlyzkoF4 x) / (1 - Real.exp (-2 * x)) =
      (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) +
        (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)) -
        (1 / (Real.exp (x / 2) + 1) +
          Real.exp (x / 2) / (Real.exp x + 1) +
          1 / (Real.exp x + 1)) := by
  let q : ℝ := Real.exp (-(x / 2))
  have hq0 : q ≠ 0 := by dsimp [q]; positivity
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqlt : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : 1 - q ^ 2 ≠ 0 := by nlinarith
  have hq4 : 1 - q ^ 4 ≠ 0 := by nlinarith [sq_nonneg (q ^ 2 - 1)]
  have hqadd : 1 + q ≠ 0 := by positivity
  have hq2add : 1 + q ^ 2 ≠ 0 := by positivity
  have hnegHalf : Real.exp (-(1 / 2 : ℝ) * x) = q := by
    dsimp [q]
    congr 1
    ring
  have hneg : Real.exp (-x) = q ^ 2 := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegTwo : Real.exp (-2 * x) = q ^ 4 := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add, hneg]
    ring
  have hposHalf : Real.exp (x / 2) = q⁻¹ := by
    calc
      Real.exp (x / 2) = Real.exp (-(-(x / 2))) := by congr 1; ring
      _ = (Real.exp (-(x / 2)))⁻¹ := Real.exp_neg _
      _ = q⁻¹ := by rfl
  have hpos : Real.exp x = (q ^ 2)⁻¹ := by
    rw [show x = -(-x) by ring, Real.exp_neg, hneg]
  have hsinh : 2 * Real.sinh (x / 2) = (1 - q ^ 2) / q := by
    rw [Real.sinh_eq, hposHalf]
    change 2 * ((q⁻¹ - q) / 2) = _
    field_simp [hq0]
  have hcosh : 2 * Real.cosh (x / 2) = (1 + q ^ 2) / q := by
    rw [Real.cosh_eq, hposHalf]
    change 2 * ((q⁻¹ + q) / 2) = _
    field_simp [hq0]
  rw [hnegTwo, hnegHalf, hsinh, hcosh, hposHalf, hpos]
  field_simp [hq0, hq2, hq4, hqadd, hq2add]
  ring

/-- The transformed complex-place Gauss kernel is integrable. -/
theorem v15OdlyzkoComplexGaussKernel_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦
        (Real.exp (-x) - Real.exp (-(1 / 2 : ℝ) * x) * v15OdlyzkoF4 x) /
          (1 - Real.exp (-x))) (Ioi 0) := by
  have h := v15OdlyzkoSinhIntegrand_integrableOn.sub
    v15OdlyzkoLogistic_half_integrableOn
  exact h.congr_fun (fun x hx ↦ (v15OdlyzkoComplexGaussKernel_eq x hx).symm)
    measurableSet_Ioi

/-- Exact evaluation of the transformed complex-place Gauss kernel. -/
theorem v15OdlyzkoComplexGaussKernel_integral :
    (∫ x in Ioi (0 : ℝ),
      (Real.exp (-x) - Real.exp (-(1 / 2 : ℝ) * x) * v15OdlyzkoF4 x) /
        (1 - Real.exp (-x))) =
      v15OdlyzkoSinhIntegral - 2 * Real.log 2 := by
  calc
    (∫ x in Ioi (0 : ℝ),
      (Real.exp (-x) - Real.exp (-(1 / 2 : ℝ) * x) * v15OdlyzkoF4 x) /
        (1 - Real.exp (-x))) =
        ∫ x in Ioi (0 : ℝ),
          ((1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) -
            1 / (Real.exp (x / 2) + 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact v15OdlyzkoComplexGaussKernel_eq x hx
    _ = v15OdlyzkoSinhIntegral - 2 * Real.log 2 := by
      rw [integral_sub v15OdlyzkoSinhIntegrand_integrableOn
        v15OdlyzkoLogistic_half_integrableOn,
        ← v15OdlyzkoSinhIntegral, v15OdlyzkoLogistic_half_integral]

/-- The transformed real-place Gauss kernel is integrable. -/
theorem v15OdlyzkoRealGaussKernel_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦
        2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
          v15OdlyzkoF4 x) / (1 - Real.exp (-2 * x))) (Ioi 0) := by
  have hsource := v15OdlyzkoSinhIntegrand_integrableOn.add
    v15OdlyzkoCoshIntegrand_integrableOn
  have helem := (v15OdlyzkoLogistic_half_integrableOn.add
    v15OdlyzkoArctanKernel_half_integrableOn).add
      v15OdlyzkoLogistic_integrableOn
  have h := hsource.sub helem
  exact h.congr_fun (fun x hx ↦ (v15OdlyzkoRealGaussKernel_eq x hx).symm)
    measurableSet_Ioi

/-- Exact evaluation of the transformed real-place Gauss kernel. -/
theorem v15OdlyzkoRealGaussKernel_integral :
    (∫ x in Ioi (0 : ℝ),
      2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
        v15OdlyzkoF4 x) / (1 - Real.exp (-2 * x))) =
      v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
        (3 * Real.log 2 + Real.pi / 2) := by
  have hsource := v15OdlyzkoSinhIntegrand_integrableOn.add
    v15OdlyzkoCoshIntegrand_integrableOn
  have helem := (v15OdlyzkoLogistic_half_integrableOn.add
    v15OdlyzkoArctanKernel_half_integrableOn).add
      v15OdlyzkoLogistic_integrableOn
  calc
    (∫ x in Ioi (0 : ℝ),
      2 * (Real.exp (-2 * x) - Real.exp (-(1 / 2 : ℝ) * x) *
        v15OdlyzkoF4 x) / (1 - Real.exp (-2 * x))) =
        ∫ x in Ioi (0 : ℝ),
          ((1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) +
            (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)) -
            (1 / (Real.exp (x / 2) + 1) +
              Real.exp (x / 2) / (Real.exp x + 1) +
              1 / (Real.exp x + 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact v15OdlyzkoRealGaussKernel_eq x hx
    _ = v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
        (3 * Real.log 2 + Real.pi / 2) := by
      let fs : ℝ → ℝ :=
        (fun y ↦ (1 - v15OdlyzkoF4 y) / (2 * Real.sinh (y / 2))) +
          (fun y ↦ (1 - v15OdlyzkoF4 y) / (2 * Real.cosh (y / 2)))
      let fe : ℝ → ℝ :=
        ((fun y ↦ 1 / (Real.exp (y / 2) + 1)) +
          (fun y ↦ Real.exp (y / 2) / (Real.exp y + 1))) +
          (fun y ↦ 1 / (Real.exp y + 1))
      have hsource' : IntegrableOn fs (Ioi 0) := by simpa [fs] using hsource
      have helem' : IntegrableOn fe (Ioi 0) := by simpa [fe] using helem
      have hsourceSplit :
          (∫ x in Ioi (0 : ℝ), fs x) =
            (∫ x in Ioi (0 : ℝ),
              (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))) +
            ∫ x in Ioi (0 : ℝ),
              (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)) := by
        simpa [fs] using integral_add v15OdlyzkoSinhIntegrand_integrableOn
          v15OdlyzkoCoshIntegrand_integrableOn
      have hpairSplit :
          (∫ x in Ioi (0 : ℝ),
            1 / (Real.exp (x / 2) + 1) +
              Real.exp (x / 2) / (Real.exp x + 1)) =
            (∫ x in Ioi (0 : ℝ), 1 / (Real.exp (x / 2) + 1)) +
            ∫ x in Ioi (0 : ℝ),
              Real.exp (x / 2) / (Real.exp x + 1) :=
        integral_add v15OdlyzkoLogistic_half_integrableOn
          v15OdlyzkoArctanKernel_half_integrableOn
      have helemSplit :
          (∫ x in Ioi (0 : ℝ), fe x) =
            ((∫ x in Ioi (0 : ℝ), 1 / (Real.exp (x / 2) + 1)) +
              ∫ x in Ioi (0 : ℝ),
                Real.exp (x / 2) / (Real.exp x + 1)) +
            ∫ x in Ioi (0 : ℝ), 1 / (Real.exp x + 1) := by
        calc
          (∫ x in Ioi (0 : ℝ), fe x) =
              (∫ x in Ioi (0 : ℝ),
                1 / (Real.exp (x / 2) + 1) +
                  Real.exp (x / 2) / (Real.exp x + 1)) +
              ∫ x in Ioi (0 : ℝ), 1 / (Real.exp x + 1) := by
                simpa [fe] using integral_add
                  (v15OdlyzkoLogistic_half_integrableOn.add
                    v15OdlyzkoArctanKernel_half_integrableOn)
                  v15OdlyzkoLogistic_integrableOn
          _ = _ := by rw [hpairSplit]
      change (∫ x in Ioi (0 : ℝ), (fs - fe) x) = _
      calc
        (∫ x in Ioi (0 : ℝ), (fs - fe) x) =
            (∫ x in Ioi (0 : ℝ), fs x) - ∫ x in Ioi (0 : ℝ), fe x :=
          integral_sub hsource' helem'
        _ = v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
            (3 * Real.log 2 + Real.pi / 2) := by
          rw [hsourceSplit, helemSplit,
            ← v15OdlyzkoSinhIntegral, ← v15OdlyzkoCoshIntegral,
            v15OdlyzkoLogistic_half_integral,
            v15OdlyzkoArctanKernel_half_integral,
            v15OdlyzkoLogistic_integral]
          ring

/-- The real part of the complex-place digamma factor is integrable against
the critical-line transform. -/
theorem v15OdlyzkoCritical_mul_re_digamma_half_integrable :
    Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t *
          (Complex.digamma
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) volume := by
  have hjoint := v15OdlyzkoCritical_mul_digammaKernel_integrable
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hinner := hjoint.integral_prod_left
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-Real.eulerMascheroniConstant)
  have hsum := hconst.add hinner
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [DedekindZeta.DigammaIntegral.re_digamma_half_integral]
  simp only [v15OdlyzkoDigammaKernel, neg_mul]
  rw [integral_const_mul]
  ring

/-- Exact complex-place digamma pairing after the justified Fubini
interchange. -/
theorem v15OdlyzkoCritical_mul_re_digamma_half_integral :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (Complex.digamma
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) =
      2 * Real.pi *
        (-Real.eulerMascheroniConstant +
          v15OdlyzkoSinhIntegral - 2 * Real.log 2) := by
  have hjoint := v15OdlyzkoCritical_mul_digammaKernel_integrable
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hinner := hjoint.integral_prod_left
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-Real.eulerMascheroniConstant)
  have hcomplexKernel :
      (∫ x in Ioi (0 : ℝ),
        (Real.exp (-x) - Real.exp (-((1 / 2 : ℝ) * x)) *
          v15OdlyzkoF4 x) / (1 - Real.exp (-x))) =
        v15OdlyzkoSinhIntegral - 2 * Real.log 2 := by
    simpa only [neg_mul] using v15OdlyzkoComplexGaussKernel_integral
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (Complex.digamma
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) =
        ∫ t : ℝ,
          (-Real.eulerMascheroniConstant * v15OdlyzkoCriticalReal t +
            ∫ x in Ioi (0 : ℝ),
              v15OdlyzkoCriticalReal t *
                v15OdlyzkoDigammaKernel (1 / 2 : ℝ) t x) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [DedekindZeta.DigammaIntegral.re_digamma_half_integral]
      simp only [v15OdlyzkoDigammaKernel, neg_mul]
      rw [integral_const_mul]
      ring
    _ = (-Real.eulerMascheroniConstant) *
          (∫ t : ℝ, v15OdlyzkoCriticalReal t) +
        ∫ t : ℝ,
          ∫ x in Ioi (0 : ℝ),
            v15OdlyzkoCriticalReal t *
              v15OdlyzkoDigammaKernel (1 / 2 : ℝ) t x := by
      rw [integral_add hconst hinner, integral_const_mul]
    _ = 2 * Real.pi *
        (-Real.eulerMascheroniConstant +
          v15OdlyzkoSinhIntegral - 2 * Real.log 2) := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        v15OdlyzkoCritical_mul_digammaKernel_fubini
          (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num),
        hcomplexKernel]
      ring

/-- The quarter-line Gauss kernel in the digamma formula agrees with the
spectrally rescaled kernel used in the Fubini theorem. -/
theorem v15OdlyzkoQuarterDigammaKernel_eq (t x : ℝ) :
    (Real.exp (-x) - Real.exp (-(1 / 4 : ℝ) * x) *
        Real.cos ((t / 2) * x)) / (1 - Real.exp (-x)) =
      v15OdlyzkoDigammaKernel (1 / 4 : ℝ) ((1 / 2 : ℝ) * t) x := by
  have hexp : -(1 / 4 : ℝ) * x = -((1 / 4 : ℝ) * x) := by ring
  have hcos : (t / 2) * x = ((1 / 2 : ℝ) * t) * x := by ring
  unfold v15OdlyzkoDigammaKernel
  rw [hexp, hcos]

/-- Rescaling the half-line variable converts the transformed quarter-line
kernel into the real-place sinh-cosh kernel. -/
theorem v15OdlyzkoQuarterGaussKernel_integral :
    (∫ x in Ioi (0 : ℝ),
      (Real.exp (-x) - Real.exp (-((1 / 4 : ℝ) * x)) *
          v15OdlyzkoF4 ((1 / 2 : ℝ) * x)) /
        (1 - Real.exp (-x))) =
      v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
        (3 * Real.log 2 + Real.pi / 2) := by
  let f : ℝ → ℝ := fun x ↦
    (Real.exp (-x) - Real.exp (-((1 / 4 : ℝ) * x)) *
        v15OdlyzkoF4 ((1 / 2 : ℝ) * x)) /
      (1 - Real.exp (-x))
  have hscale := integral_comp_mul_left_Ioi f 0
    (by norm_num : (0 : ℝ) < 2)
  have hscale' :
      (∫ x in Ioi (0 : ℝ), f (2 * x)) =
        (2 : ℝ)⁻¹ • ∫ x in Ioi (0 : ℝ), f x := by
    simpa only [mul_zero] using hscale
  change (∫ x in Ioi (0 : ℝ), f x) = _
  calc
    (∫ x in Ioi (0 : ℝ), f x) =
        2 * ∫ x in Ioi (0 : ℝ), f (2 * x) := by
      rw [hscale']
      norm_num [smul_eq_mul]
      ring
    _ = ∫ x in Ioi (0 : ℝ), 2 * f (2 * x) := by
      rw [integral_const_mul]
    _ = ∫ x in Ioi (0 : ℝ),
        2 * (Real.exp (-2 * x) -
            Real.exp (-(1 / 2 : ℝ) * x) * v15OdlyzkoF4 x) /
          (1 - Real.exp (-2 * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp [f]
      rw [show -(2 * x) = -2 * x by ring,
        show -((1 / 4 : ℝ) * (2 * x)) = -(1 / 2 : ℝ) * x by ring,
        show (1 / 2 : ℝ) * (2 * x) = x by ring]
      ring
    _ = v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
        (3 * Real.log 2 + Real.pi / 2) :=
      v15OdlyzkoRealGaussKernel_integral

/-- The real part of the real-place digamma factor is integrable against the
critical-line transform. -/
theorem v15OdlyzkoCritical_mul_re_digamma_quarter_integrable :
    Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t *
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) volume := by
  have hjoint := v15OdlyzkoCritical_mul_digammaKernel_scaled_integrable
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (1 / 2 : ℝ)
  have hinner := hjoint.integral_prod_left
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-Real.eulerMascheroniConstant)
  have hsum := hconst.add hinner
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [DedekindZeta.DigammaIntegral.re_digamma_quarter_integral]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x _ ↦ v15OdlyzkoQuarterDigammaKernel_eq t x)]
  rw [integral_const_mul]
  ring

/-- Exact real-place digamma pairing after spectral and half-line
rescaling. -/
theorem v15OdlyzkoCritical_mul_re_digamma_quarter_integral :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (Complex.digamma
          ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) =
      2 * Real.pi *
        (-Real.eulerMascheroniConstant +
          v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
            (3 * Real.log 2 + Real.pi / 2)) := by
  have hjoint := v15OdlyzkoCritical_mul_digammaKernel_scaled_integrable
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (1 / 2 : ℝ)
  have hinner := hjoint.integral_prod_left
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-Real.eulerMascheroniConstant)
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (Complex.digamma
          ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) =
        ∫ t : ℝ,
          (-Real.eulerMascheroniConstant * v15OdlyzkoCriticalReal t +
            ∫ x in Ioi (0 : ℝ),
              v15OdlyzkoCriticalReal t *
                v15OdlyzkoDigammaKernel (1 / 4 : ℝ)
                  ((1 / 2 : ℝ) * t) x) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [DedekindZeta.DigammaIntegral.re_digamma_quarter_integral]
      rw [setIntegral_congr_fun measurableSet_Ioi
        (fun x _ ↦ v15OdlyzkoQuarterDigammaKernel_eq t x)]
      rw [integral_const_mul]
      ring
    _ = (-Real.eulerMascheroniConstant) *
          (∫ t : ℝ, v15OdlyzkoCriticalReal t) +
        ∫ t : ℝ,
          ∫ x in Ioi (0 : ℝ),
            v15OdlyzkoCriticalReal t *
              v15OdlyzkoDigammaKernel (1 / 4 : ℝ)
                ((1 / 2 : ℝ) * t) x := by
      rw [integral_add hconst hinner, integral_const_mul]
    _ = 2 * Real.pi *
        (-Real.eulerMascheroniConstant +
          v15OdlyzkoSinhIntegral + v15OdlyzkoCoshIntegral -
            (3 * Real.log 2 + Real.pi / 2)) := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        v15OdlyzkoCritical_mul_digammaKernel_scaled_fubini
          (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (1 / 2 : ℝ),
        v15OdlyzkoQuarterGaussKernel_integral]
      ring

/-- Elementary logarithmic normalization used to identify the source
constant `B`. -/
theorem v15Odlyzko_log_eight_pi :
    Real.log (8 * Real.pi) =
      Real.log (2 * Real.pi) + 2 * Real.log 2 := by
  calc
    Real.log (8 * Real.pi) = Real.log 8 + Real.log Real.pi := by
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) Real.pi_ne_zero]
    _ = 3 * Real.log 2 + Real.log Real.pi := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    _ = (Real.log 2 + Real.log Real.pi) + 2 * Real.log 2 := by ring
    _ = Real.log (2 * Real.pi) + 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]

/-- The real-place bracket is integrable against the critical transform. -/
theorem v15OdlyzkoCritical_mul_realPlaceBracket_integrable :
    Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t *
          (-Real.log Real.pi +
            (Complex.digamma
              ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) volume := by
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-Real.log Real.pi)
  have hsum := hconst.add
    v15OdlyzkoCritical_mul_re_digamma_quarter_integrable
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

/-- The real-place bracket pairs to `-A` in the source normalization. -/
theorem v15OdlyzkoCritical_mul_realPlaceBracket_integral :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (-Real.log Real.pi +
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) =
      -(2 * Real.pi) * v15OdlyzkoArchLogA := by
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-Real.log Real.pi)
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (-Real.log Real.pi +
          (Complex.digamma
            ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) =
        ∫ t : ℝ,
          (-Real.log Real.pi * v15OdlyzkoCriticalReal t +
            v15OdlyzkoCriticalReal t *
              (Complex.digamma
                ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) := by
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = (-Real.log Real.pi) *
          (∫ t : ℝ, v15OdlyzkoCriticalReal t) +
        ∫ t : ℝ,
          v15OdlyzkoCriticalReal t *
            (Complex.digamma
              ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re := by
      rw [integral_add hconst
        v15OdlyzkoCritical_mul_re_digamma_quarter_integrable,
        integral_const_mul]
    _ = -(2 * Real.pi) * v15OdlyzkoArchLogA := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        v15OdlyzkoCritical_mul_re_digamma_quarter_integral]
      unfold v15OdlyzkoArchLogA v15OdlyzkoArchLogB
      rw [v15Odlyzko_log_eight_pi]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
      ring

/-- The complex-place bracket is integrable against the critical transform. -/
theorem v15OdlyzkoCritical_mul_complexPlaceBracket_integrable :
    Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t *
          (-2 * Real.log (2 * Real.pi) +
            2 * (Complex.digamma
              ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re)) volume := by
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-2 * Real.log (2 * Real.pi))
  have hdigamma :=
    v15OdlyzkoCritical_mul_re_digamma_half_integrable.const_mul 2
  have hsum := hconst.add hdigamma
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

/-- The complex-place bracket pairs to `-2B` in the source normalization. -/
theorem v15OdlyzkoCritical_mul_complexPlaceBracket_integral :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (-2 * Real.log (2 * Real.pi) +
          2 * (Complex.digamma
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re)) =
      -(4 * Real.pi) * v15OdlyzkoArchLogB := by
  have hconst := v15OdlyzkoCriticalReal_integrable.const_mul
    (-2 * Real.log (2 * Real.pi))
  have hdigamma :=
    v15OdlyzkoCritical_mul_re_digamma_half_integrable.const_mul 2
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (-2 * Real.log (2 * Real.pi) +
          2 * (Complex.digamma
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re)) =
        ∫ t : ℝ,
          (-2 * Real.log (2 * Real.pi) * v15OdlyzkoCriticalReal t +
            2 * (v15OdlyzkoCriticalReal t *
              (Complex.digamma
                ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re)) := by
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = (-2 * Real.log (2 * Real.pi)) *
          (∫ t : ℝ, v15OdlyzkoCriticalReal t) +
        2 * ∫ t : ℝ,
          v15OdlyzkoCriticalReal t *
            (Complex.digamma
              ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
      rw [integral_add hconst hdigamma, integral_const_mul,
        integral_const_mul]
    _ = -(4 * Real.pi) * v15OdlyzkoArchLogB := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        v15OdlyzkoCritical_mul_re_digamma_half_integral]
      unfold v15OdlyzkoArchLogB
      rw [v15Odlyzko_log_eight_pi]
      ring

/-- Real-part form of the proved symmetric logarithmic-derivative identity. -/
theorem v15OdlyzkoArchimedeanBracket_re_eq
    (K : Type*) [Field K] [NumberField K] (t : ℝ) :
    (logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
        logDeriv (DedekindZeta.ZInfty K)
          ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re =
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) +
        (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          (-Real.log Real.pi +
            (Complex.digamma
              ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re) +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
          (-2 * Real.log (2 * Real.pi) +
            2 * (Complex.digamma
              ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re) := by
  rw [DedekindZeta.DigammaIdentities.logDeriv_ZInfty_critical_bracket]
  simp [Complex.log_re, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The full real archimedean bracket is integrable against the critical
transform for every number field. -/
theorem v15OdlyzkoCritical_mul_archimedeanBracket_re_integrable
    (K : Type*) [Field K] [NumberField K] :
    Integrable
      (fun t : ℝ ↦
        v15OdlyzkoCriticalReal t *
          (logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
            logDeriv (DedekindZeta.ZInfty K)
              ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re) volume := by
  let logD : ℝ := Real.log (((|NumberField.discr K| : ℤ) : ℝ))
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  let c : ℝ := NumberField.InfinitePlace.nrComplexPlaces K
  have hdisc := v15OdlyzkoCriticalReal_integrable.const_mul logD
  have hreal :=
    v15OdlyzkoCritical_mul_realPlaceBracket_integrable.const_mul r
  have hcomplex :=
    v15OdlyzkoCritical_mul_complexPlaceBracket_integrable.const_mul c
  have hsum := (hdisc.add hreal).add hcomplex
  apply hsum.congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [v15OdlyzkoArchimedeanBracket_re_eq K t]
  dsimp only [logD, r, c]
  ring

/-- Exact pairing of the proved number-field archimedean bracket with the
Odlyzko transform. -/
theorem v15OdlyzkoCritical_mul_archimedeanBracket_re_integral
    (K : Type*) [Field K] [NumberField K] :
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
          logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re) =
      2 * Real.pi *
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            v15OdlyzkoArchLogA -
          2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
            v15OdlyzkoArchLogB) := by
  let logD : ℝ := Real.log (((|NumberField.discr K| : ℤ) : ℝ))
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  let c : ℝ := NumberField.InfinitePlace.nrComplexPlaces K
  have hdisc := v15OdlyzkoCriticalReal_integrable.const_mul logD
  have hreal :=
    v15OdlyzkoCritical_mul_realPlaceBracket_integrable.const_mul r
  have hcomplex :=
    v15OdlyzkoCritical_mul_complexPlaceBracket_integrable.const_mul c
  calc
    (∫ t : ℝ,
      v15OdlyzkoCriticalReal t *
        (logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
          logDeriv (DedekindZeta.ZInfty K)
            ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re) =
        ∫ t : ℝ,
          (logD * v15OdlyzkoCriticalReal t +
            r * (v15OdlyzkoCriticalReal t *
              (-Real.log Real.pi +
                (Complex.digamma
                  ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) +
            c * (v15OdlyzkoCriticalReal t *
              (-2 * Real.log (2 * Real.pi) +
                2 * (Complex.digamma
                  ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re))) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [v15OdlyzkoArchimedeanBracket_re_eq K t]
      dsimp only [logD, r, c]
      ring
    _ = logD * (∫ t : ℝ, v15OdlyzkoCriticalReal t) +
        r * (∫ t : ℝ,
          v15OdlyzkoCriticalReal t *
            (-Real.log Real.pi +
              (Complex.digamma
                ((1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I)).re)) +
        c * (∫ t : ℝ,
          v15OdlyzkoCriticalReal t *
            (-2 * Real.log (2 * Real.pi) +
              2 * (Complex.digamma
                ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re)) := by
      have houter := integral_add (hdisc.add hreal) hcomplex
      have hinner := integral_add hdisc hreal
      have hsplit := houter.trans (congrArg (fun u : ℝ ↦
        u + ∫ t : ℝ,
          c * (v15OdlyzkoCriticalReal t *
            (-2 * Real.log (2 * Real.pi) +
              2 * (Complex.digamma
                ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re))) hinner)
      simpa only [Pi.add_apply, integral_const_mul] using hsplit
    _ = 2 * Real.pi *
        (Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
          (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
            v15OdlyzkoArchLogA -
          2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
            v15OdlyzkoArchLogB) := by
      rw [show (∫ t : ℝ, v15OdlyzkoCriticalReal t) =
          2 * Real.pi by
        simpa [v15OdlyzkoCriticalReal] using
          v15OdlyzkoPhi_critical_re_integral,
        v15OdlyzkoCritical_mul_realPlaceBracket_integral,
        v15OdlyzkoCritical_mul_complexPlaceBracket_integral]
      dsimp only [logD, r, c]
      ring

/-- Normalized form of the archimedean pairing used in the explicit formula. -/
theorem v15OdlyzkoCritical_archimedeanBracket_re_average
    (K : Type*) [Field K] [NumberField K] :
    (1 / (2 * Real.pi)) *
        (∫ t : ℝ,
          v15OdlyzkoCriticalReal t *
            (logDeriv (DedekindZeta.ZInfty K)
                ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
              logDeriv (DedekindZeta.ZInfty K)
                ((1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re) =
      Real.log (((|NumberField.discr K| : ℤ) : ℝ)) -
        (NumberField.InfinitePlace.nrRealPlaces K : ℝ) *
          v15OdlyzkoArchLogA -
        2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) *
          v15OdlyzkoArchLogB := by
  rw [v15OdlyzkoCritical_mul_archimedeanBracket_re_integral K]
  field_simp [Real.pi_ne_zero]

end

end TraceEuclidean
