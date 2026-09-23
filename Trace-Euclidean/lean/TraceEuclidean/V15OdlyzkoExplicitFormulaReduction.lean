import TraceEuclidean.V15OdlyzkoAnalyticBridge
import TraceEuclidean.V15OdlyzkoPhiEndpoint
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.DSlope

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Source-exact analytic inputs for Odlyzko's Table 4 row

Odlyzko's 1990 survey, equation (2.3), separates the explicit formula into
two archimedean integrals, the exact endpoint error, a zero contribution,
and a prime-ideal contribution.  The elementary endpoint and prime terms
are proved elsewhere in this project.  This module records the remaining
analytic statements with their exact normalizations and proves that they
imply the previously used Table 4 interface.

This module does not assert the analytic inputs.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory

/-- The archimedean integral multiplied by the field degree in (2.3). -/
def v15OdlyzkoSinhIntegral : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))

/-- The archimedean integral multiplied by the number of real places in (2.3). -/
def v15OdlyzkoCoshIntegral : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2))

/-- A cancellation-friendly form of the sinh integrand on the positive axis. -/
theorem v15OdlyzkoSinhIntegrand_eq (x : ℝ) (hx : 0 < x) :
    (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) =
      (Real.cosh (x / 2) - v15OdlyzkoH (x / 4)) / Real.sinh x := by
  have hs : Real.sinh (x / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
  have hc : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hsx : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hdouble : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    conv_lhs => rw [show x = 2 * (x / 2) by ring, Real.sinh_two_mul]
  rw [v15OdlyzkoF4, hdouble]
  field_simp

/-- A denominator without a removable singularity for the cosh integrand. -/
theorem v15OdlyzkoCoshIntegrand_eq (x : ℝ) :
    (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)) =
      (Real.cosh (x / 2) - v15OdlyzkoH (x / 4)) /
        (1 + Real.cosh x) := by
  have hc : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hdouble : 1 + Real.cosh x = 2 * Real.cosh (x / 2) ^ 2 := by
    conv_lhs => rw [show x = 2 * (x / 2) by ring, Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hd : 1 + Real.cosh x ≠ 0 := by positivity
  rw [v15OdlyzkoF4, hdouble]
  field_simp

private theorem v15OdlyzkoF4_deriv_zero : deriv v15OdlyzkoF4 0 = 0 := by
  have h := (v15OdlyzkoF4_differentiable 0).hasDerivAt
  have hneg : HasDerivAt (fun x : ℝ ↦ v15OdlyzkoF4 (-x))
      (-deriv v15OdlyzkoF4 0) 0 := by
    have h' : HasDerivAt v15OdlyzkoF4 (deriv v15OdlyzkoF4 0) (-(0 : ℝ)) := by
      simpa using h
    simpa [Function.comp_def] using
      h'.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
  have heq : (fun x : ℝ ↦ v15OdlyzkoF4 (-x)) = v15OdlyzkoF4 := by
    funext x
    exact v15OdlyzkoF4_even x
  rw [heq] at hneg
  have hu := hneg.unique h
  linarith

/-- The apparent singularity at the origin in the sinh integral is removable. -/
theorem v15OdlyzkoSinhIntegrand_continuousAt_zero :
    ContinuousAt
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))) 0 := by
  let a : ℝ → ℝ := fun x ↦ 1 - v15OdlyzkoF4 x
  let b : ℝ → ℝ := fun x ↦ 2 * Real.sinh (x / 2)
  have ha : HasDerivAt a 0 0 := by
    have h := ((v15OdlyzkoF4_differentiable 0).hasDerivAt).const_sub (1 : ℝ)
    simpa [a, v15OdlyzkoF4_deriv_zero] using h
  have hb : HasDerivAt b 1 0 := by
    have h := ((Real.hasDerivAt_sinh ((0 : ℝ) / 2)).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const 2)).const_mul 2
    simpa [b] using h
  have hca : ContinuousAt (dslope a 0) 0 := continuousAt_dslope_same.mpr ha.differentiableAt
  have hcb : ContinuousAt (dslope b 0) 0 := continuousAt_dslope_same.mpr hb.differentiableAt
  have hb0 : dslope b 0 0 ≠ 0 := by simpa [dslope_same, hb.deriv] using (one_ne_zero : (1 : ℝ) ≠ 0)
  have heq :
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))) =
        (fun x ↦ dslope a 0 x / dslope b 0 x) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [a, b, dslope_same, ha.deriv, hb.deriv, v15OdlyzkoF4_zero]
    · rw [dslope_of_ne a hx, dslope_of_ne b hx]
      simp only [slope_def_field]
      simp [a, b, v15OdlyzkoF4_zero, Real.sinh_zero]
      field_simp
  rw [heq]
  exact hca.div hcb hb0

/-- A quadratic lower bound for the source's trigonometric auxiliary kernel. -/
theorem v15OdlyzkoHCore_lower_quadratic {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    1 - Real.pi ^ 2 * t ^ 2 / 6 ≤ v15OdlyzkoHCore t := by
  have harg : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi * t)
  have hs := Real.sin_ge_sub_cube harg
  have hc' := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ (2 - t) / 6 by positivity)
  have hs' := div_le_div_of_nonneg_right hs
    (show 0 ≤ 2 * Real.pi by positivity)
  unfold v15OdlyzkoHCore
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hid :
      (2 - t) / 3 + (2 - t) / 6 * (1 - (Real.pi * t) ^ 2 / 2) +
        (Real.pi * t - (Real.pi * t) ^ 3 / 6) / (2 * Real.pi) =
        1 - Real.pi ^ 2 * t ^ 2 / 6 := by
    field_simp
    ring
  rw [← hid]
  linarith [hc', hs']

/-- A simple local bound that removes numerical cancellation at the origin. -/
theorem v15OdlyzkoSinhIntegrand_le_half_x {x : ℝ}
    (hx0 : 0 ≤ x) (hxsmall : x ≤ 1 / 100) :
    (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) ≤ x / 2 := by
  by_cases hx : x = 0
  · subst x
    simp [v15OdlyzkoF4_zero]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have ht0 : 0 ≤ x / 4 := by positivity
  have ht2 : x / 4 ≤ 2 := by linarith
  have hH : 1 - Real.pi ^ 2 * (x / 4) ^ 2 / 6 ≤ v15OdlyzkoH (x / 4) := by
    simpa [v15OdlyzkoH, abs_of_nonneg ht0, ht2] using
      (v15OdlyzkoHCore_lower_quadratic ht0 ht2)
  have hπ : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hH' : 1 - x ^ 2 / 6 ≤ v15OdlyzkoH (x / 4) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hπ) (sq_nonneg x)]
  have hz : |x ^ 2 / 8| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg x]
  have he := Real.abs_exp_sub_one_le hz
  have he' : Real.exp (x ^ 2 / 8) - 1 ≤ x ^ 2 / 4 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ x ^ 2 / 8)] at he
    exact (abs_le.mp he).2.trans_eq (by ring)
  have hcosh : Real.cosh (x / 2) - 1 ≤ x ^ 2 / 4 := by
    have h := Real.cosh_le_exp_half_sq (x / 2)
    rw [show (x / 2) ^ 2 / 2 = x ^ 2 / 8 by ring] at h
    linarith
  have hnum : Real.cosh (x / 2) - v15OdlyzkoH (x / 4) ≤ x ^ 2 / 2 := by
    nlinarith [sq_nonneg x]
  have hden : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0
  have hdenpos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hxpos
  rw [v15OdlyzkoSinhIntegrand_eq x hxpos]
  apply (div_le_iff₀ hdenpos).2
  nlinarith [mul_nonneg (show 0 ≤ x / 2 by positivity) (sub_nonneg.mpr hden)]

/-- The source's sinh-denominator archimedean integral converges. -/
theorem v15OdlyzkoSinhIntegrand_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      (Set.Ioi 0) := by
  let f : ℝ → ℝ := fun x ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))
  have hcont : ContinuousOn f (Set.Ici 0) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact v15OdlyzkoSinhIntegrand_continuousAt_zero.continuousWithinAt
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hden : 2 * Real.sinh (x / 2) ≠ 0 := by
        positivity
      have hnum : ContinuousAt (fun y : ℝ ↦ 1 - v15OdlyzkoF4 y) x :=
        (continuous_const.sub v15OdlyzkoF4_continuous).continuousAt
      have hdencont : ContinuousAt (fun y : ℝ ↦ 2 * Real.sinh (y / 2)) x :=
        (continuous_const.mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2))).continuousAt
      exact (hnum.div hdencont hden).continuousWithinAt
  have hbig : f =O[Filter.atTop] (fun x : ℝ ↦ Real.exp (-(1 / 2) * x)) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop (9 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hF : v15OdlyzkoF4 x = 0 := by
      apply v15OdlyzkoF4_eq_zero_of_eight_lt_abs
      rw [abs_of_pos hxpos]
      linarith
    have he : 2 ≤ Real.exp (x / 2) := by
      have := Real.add_one_le_exp (x / 2)
      linarith
    have hep : 0 < Real.exp (x / 2) := Real.exp_pos _
    have hinv : (Real.exp (x / 2))⁻¹ ≤ Real.exp (x / 2) / 2 := by
      have hp : 0 ≤ (Real.exp (x / 2))⁻¹ := (inv_pos.mpr hep).le
      have hm := mul_inv_cancel₀ hep.ne'
      nlinarith [mul_nonneg (sub_nonneg.mpr he) hp]
    have hdenlower : Real.exp (x / 2) / 2 ≤ 2 * Real.sinh (x / 2) := by
      rw [Real.sinh_eq, Real.exp_neg]
      linarith
    have hdenpos : 0 < 2 * Real.sinh (x / 2) := by
      have : 0 < Real.exp (x / 2) / 2 := by positivity
      linarith
    have hmain : 1 / (2 * Real.sinh (x / 2)) ≤
        2 * Real.exp (-(1 / 2) * x) := by
      calc
        1 / (2 * Real.sinh (x / 2)) ≤ 1 / (Real.exp (x / 2) / 2) :=
          one_div_le_one_div_of_le (by positivity) hdenlower
        _ = 2 * Real.exp (-(1 / 2) * x) := by
          rw [show -(1 / 2 : ℝ) * x = -(x / 2) by ring, Real.exp_neg]
          field_simp
    have hnorm : ‖f x‖ = 1 / (2 * Real.sinh (x / 2)) := by
      change ‖(1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))‖ = _
      rw [hF, sub_zero, Real.norm_eq_abs, abs_div, abs_one,
        abs_of_pos hdenpos]
    rw [hnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hmain
  exact integrable_of_isBigO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)
    hcont hbig

/-- The removable singularity contributes at most `1/40000` on `[0, 1/100]`. -/
theorem v15OdlyzkoSinhIntegral_zero_hundredth_le :
    (∫ x in (0 : ℝ)..(1 / 100 : ℝ),
      (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤ 1 / 40000 := by
  have hf : IntervalIntegrable
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      volume 0 (1 / 100) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 100)]
    exact v15OdlyzkoSinhIntegrand_integrableOn.mono_set Set.Ioc_subset_Ioi_self
  have hg : IntervalIntegrable (fun x : ℝ ↦ x / 2) volume 0 (1 / 100) :=
    (continuous_id.div_const 2).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1 / 100) hf hg (fun x hx ↦
      v15OdlyzkoSinhIntegrand_le_half_x hx.1 hx.2)
  have hder (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 4) (x / 2) x := by
    have h : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 4) (2 * x / 4) x := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
        (hasDerivAt_pow 2 x).div_const 4
    have heq : 2 * x / 4 = x / 2 := by ring
    rw [← heq]
    exact h
  have hval : (∫ x in (0 : ℝ)..(1 / 100 : ℝ), x / 2) = 1 / 40000 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hder x) hg]
    norm_num
  rw [hval] at hmono
  exact hmono

private theorem v15OdlyzkoExpNegEight_le : Real.exp (-8) ≤ 1 / 1000 := by
  have h1 : (5 / 2 : ℝ) ≤ Real.exp 1 :=
    (by norm_num : (5 / 2 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9 |>.le
  have hpow : (5 / 2 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 :=
    pow_le_pow_left₀ (by norm_num) h1 8
  have h8 : (1000 : ℝ) ≤ Real.exp 8 := by
    have heq : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
      convert Real.exp_nat_mul (1 : ℝ) 8 using 1 <;> norm_num
    rw [heq]
    nlinarith [hpow]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) h8

/-- A rational upper bound for the common exponential tail factor. -/
theorem v15OdlyzkoExpNegFour_le : Real.exp (-4) ≤ 18316 / 1000000 := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have hpow : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) h1 4
  have h4 : (1000000 / 18316 : ℝ) ≤ Real.exp 4 := by
    have heq : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
      convert Real.exp_nat_mul (1 : ℝ) 4 using 1 <;> norm_num
    rw [heq]
    nlinarith [hpow]
  rw [Real.exp_neg]
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000000 / 18316) h4
  have heq : (1 : ℝ) / (1000000 / 18316) = 18316 / 1000000 := by norm_num
  rw [heq] at this
  simpa only [one_div] using this

/-- A uniform exponential majorant for the sinh tail beyond `x = 8`. -/
theorem v15OdlyzkoSinhIntegrand_tail_pointwise {x : ℝ} (hx : 8 < x) :
    (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)) ≤
      (1000 / 999) * Real.exp ((-1 / 2) * x) := by
  have hxpos : 0 < x := by linarith
  have hF : v15OdlyzkoF4 x = 0 := by
    apply v15OdlyzkoF4_eq_zero_of_eight_lt_abs
    rwa [abs_of_pos hxpos]
  have hsmall : Real.exp (-x) ≤ 1 / 1000 := by
    exact (Real.exp_le_exp.mpr (by linarith : -x ≤ (-8 : ℝ))).trans
      v15OdlyzkoExpNegEight_le
  have hid : 2 * Real.sinh (x / 2) =
      Real.exp (x / 2) * (1 - Real.exp (-x)) := by
    rw [Real.sinh_eq]
    have heq : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith [heq]
  have hfactor : (999 / 1000 : ℝ) ≤ 1 - Real.exp (-x) := by linarith
  have hden : (999 / 1000 : ℝ) * Real.exp (x / 2) ≤
      2 * Real.sinh (x / 2) := by
    rw [hid]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hfactor (Real.exp_pos (x / 2)).le
  rw [hF, sub_zero]
  calc
    1 / (2 * Real.sinh (x / 2)) ≤
        1 / ((999 / 1000 : ℝ) * Real.exp (x / 2)) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = (1000 / 999) * Real.exp ((-1 / 2) * x) := by
      rw [show (-1 / 2 : ℝ) * x = -(x / 2) by ring, Real.exp_neg]
      field_simp [(Real.exp_pos (x / 2)).ne']

/-- A rigorous tail bound for the sinh integral. -/
theorem v15OdlyzkoSinhIntegral_tail_le :
    (∫ x in Set.Ioi (8 : ℝ),
      (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2))) ≤
      (2000 / 999) * Real.exp (-4) := by
  have hf : IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      (Set.Ioi 8) :=
    v15OdlyzkoSinhIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 8) hx)
  have hg : IntegrableOn
      (fun x : ℝ ↦ (1000 / 999 : ℝ) * Real.exp ((-1 / 2) * x))
      (Set.Ioi 8) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 8).const_mul _
  have hmono := setIntegral_mono_on (s := Set.Ioi (8 : ℝ)) hf hg measurableSet_Ioi
    (fun x hx ↦ v15OdlyzkoSinhIntegrand_tail_pointwise hx)
  have hval :
      (∫ x in Set.Ioi (8 : ℝ),
        (1000 / 999 : ℝ) * Real.exp ((-1 / 2) * x)) =
        (2000 / 999) * Real.exp (-4) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 8]
    ring
  rw [hval] at hmono
  exact hmono

/-- The source's cosh-denominator archimedean integral converges. -/
theorem v15OdlyzkoCoshIntegrand_integrable :
    Integrable
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)))
      volume := by
  obtain ⟨C, hC⟩ := v15OdlyzkoF4_continuous.bounded_above_of_compact_support
    v15OdlyzkoF4_hasCompactSupport
  have hfactor :
      Integrable (fun x : ℝ ↦ v15OdlyzkoSech x * (1 - v15OdlyzkoF4 x))
        volume := by
    apply v15OdlyzkoSech_integrable.mul_bdd
    · exact (continuous_const.sub v15OdlyzkoF4_continuous).aestronglyMeasurable
    · filter_upwards with x
      have := hC x
      calc
        ‖1 - v15OdlyzkoF4 x‖ ≤ ‖(1 : ℝ)‖ + ‖v15OdlyzkoF4 x‖ := norm_sub_le _ _
        _ ≤ 1 + C := by simpa using add_le_add_left this 1
  have hscaled :
      Integrable
        (fun x : ℝ ↦ (1 / 2 : ℝ) *
          (v15OdlyzkoSech x * (1 - v15OdlyzkoF4 x))) volume :=
    hfactor.const_mul (1 / 2 : ℝ)
  convert hscaled using 1
  funext x
  unfold v15OdlyzkoSech
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem v15OdlyzkoCoshIntegrand_integrableOn :
    IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)))
      (Set.Ioi 0) :=
    v15OdlyzkoCoshIntegrand_integrable.integrableOn

/-- An explicit majorant for the cosh tail beyond the support of the kernel. -/
theorem v15OdlyzkoCoshIntegral_tail_le :
    (∫ x in Set.Ioi (8 : ℝ),
      (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2))) ≤
      2 * Real.exp (-4) := by
  have hf : IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.cosh (x / 2)))
      (Set.Ioi 8) :=
    v15OdlyzkoCoshIntegrand_integrableOn.mono_set
      (fun x hx ↦ lt_trans (by norm_num : (0 : ℝ) < 8) hx)
  have hg : IntegrableOn (fun x : ℝ ↦ Real.exp ((-1 / 2) * x))
      (Set.Ioi 8) := integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 8
  have hmono := setIntegral_mono_on (s := Set.Ioi (8 : ℝ)) hf hg measurableSet_Ioi
    (fun x hx ↦ by
      have hxpos : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 8) hx
      have hF : v15OdlyzkoF4 x = 0 := by
        apply v15OdlyzkoF4_eq_zero_of_eight_lt_abs
        rwa [abs_of_pos hxpos]
      rw [hF, sub_zero]
      have he : 0 < Real.exp (x / 2) := Real.exp_pos _
      have hd : Real.exp (x / 2) ≤ 2 * Real.cosh (x / 2) := by
        rw [Real.cosh_eq]
        linarith [Real.exp_pos (-(x / 2))]
      calc
        1 / (2 * Real.cosh (x / 2)) ≤ 1 / Real.exp (x / 2) :=
          one_div_le_one_div_of_le he hd
        _ = Real.exp ((-1 / 2) * x) := by
          rw [show (-1 / 2 : ℝ) * x = -(x / 2) by ring, Real.exp_neg]
          simp only [one_div])
  have hval :
      (∫ x in Set.Ioi (8 : ℝ), Real.exp ((-1 / 2) * x)) =
        2 * Real.exp (-4) := by
    rw [integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 8]
    ring
  rw [hval] at hmono
  exact hmono

/-- The exact logarithmic constant per complex-signature dimension. -/
def v15OdlyzkoArchLogB : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    v15OdlyzkoSinhIntegral

/-- The exact logarithmic constant per real place. -/
def v15OdlyzkoArchLogA : ℝ :=
  Real.pi / 2 + v15OdlyzkoArchLogB - v15OdlyzkoCoshIntegral

/-- A strict certificate for both table constants.  The remaining sinh
integrability is included so the inequality cannot rely on the Bochner
integral's fallback value for a nonintegrable function; cosh integrability
is already proved. -/
def V15OdlyzkoABIntegralCertificate : Prop :=
  IntegrableOn
      (fun x : ℝ ↦ (1 - v15OdlyzkoF4 x) / (2 * Real.sinh (x / 2)))
      (Set.Ioi 0) ∧
    Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA ∧
    Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB

/-- With convergence proved, only the two strict numerical inequalities remain
to construct the full source-normalized archimedean certificate. -/
theorem v15OdlyzkoABIntegralCertificate_of_strictBounds
    (hA : Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA)
    (hB : Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB) :
    V15OdlyzkoABIntegralCertificate :=
  ⟨v15OdlyzkoSinhIntegrand_integrableOn, hA, hB⟩

/-- Equation (2.3) with the exact `b=4` endpoint term and complete prime
correction. The parameter `Z` must be supplied by a convergent zero sum
in the source's normalization; an unordered occurrence sum is supported. -/
def V15OdlyzkoExplicitFormulaInput (Z : CodedNumberField → ℝ) : Prop :=
  ∀ K : CodedNumberField,
    Real.log (((|K.discriminant| : ℤ) : ℝ)) =
      (NumberField.InfinitePlace.nrRealPlaces K.1 : ℝ) * Real.pi / 2 +
      (Module.finrank ℚ K.1 : ℝ) *
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) -
      (Module.finrank ℚ K.1 : ℝ) * v15OdlyzkoSinhIntegral -
      (NumberField.InfinitePlace.nrRealPlaces K.1 : ℝ) *
        v15OdlyzkoCoshIntegral -
      4 * (∫ x in Set.Ioi (0 : ℝ),
        v15OdlyzkoF4 x * Real.cosh (x / 2)) +
      Z K + v15OdlyzkoPrimeCorrection K.1

/-- The explicit formula, nonnegative zero term, and certified strict
archimedean constants imply the exact-error Table 4 inequality with the
already formalized complete prime-ideal correction. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula
    (Z : CodedNumberField → ℝ)
    (hFormula : V15OdlyzkoExplicitFormulaInput Z)
    (hZeros : ∀ K, 0 ≤ Z K)
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  intro K
  let r : ℕ := NumberField.InfinitePlace.nrRealPlaces K.1
  let c : ℕ := 2 * NumberField.InfinitePlace.nrComplexPlaces K.1
  have hrank : r + c = Module.finrank ℚ K.1 := by
    simpa [r, c] using
      (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K.1)
  have hpos : 0 < r + c := by
    rw [hrank]
    exact Module.finrank_pos
  have hA : Real.log (36347 / 1000 : ℝ) < v15OdlyzkoArchLogA := hAB.2.1
  have hB : Real.log (16593 / 1000 : ℝ) < v15OdlyzkoArchLogB := hAB.2.2
  have hStrict :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
        (c : ℝ) * Real.log (16593 / 1000 : ℝ) <
      (r : ℝ) * v15OdlyzkoArchLogA +
        (c : ℝ) * v15OdlyzkoArchLogB := by
    have ha := mul_le_mul_of_nonneg_left hA.le (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hb := mul_le_mul_of_nonneg_left hB.le (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    by_cases hr : r = 0
    · have hcpos : (0 : ℝ) < c := by
        exact_mod_cast (by omega : 0 < c)
      have hb' := mul_lt_mul_of_pos_left hB hcpos
      simp [hr] at ha ⊢
      linarith
    · have hrpos : (0 : ℝ) < r := by
        exact_mod_cast (Nat.pos_of_ne_zero hr)
      have ha' := mul_lt_mul_of_pos_left hA hrpos
      linarith
  have hdegree : (Module.finrank ℚ K.1 : ℝ) = (r : ℝ) + (c : ℝ) := by
    exact_mod_cast hrank.symm
  have hLogD :
      Real.log (((|K.discriminant| : ℤ) : ℝ)) =
        (r : ℝ) * v15OdlyzkoArchLogA +
          (c : ℝ) * v15OdlyzkoArchLogB -
          (32 / 3 : ℝ) + Z K + v15OdlyzkoPrimeCorrection K.1 := by
    have h := hFormula K
    rw [show 4 * (∫ x in Set.Ioi (0 : ℝ),
        v15OdlyzkoF4 x * Real.cosh (x / 2)) = (32 / 3 : ℝ) from
      v15OdlyzkoF4_archimedean_error_integral] at h
    change Real.log (((|K.discriminant| : ℤ) : ℝ)) =
      (r : ℝ) * Real.pi / 2 +
      (Module.finrank ℚ K.1 : ℝ) *
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) -
      (Module.finrank ℚ K.1 : ℝ) * v15OdlyzkoSinhIntegral -
      (r : ℝ) * v15OdlyzkoCoshIntegral -
      (32 / 3 : ℝ) + Z K + v15OdlyzkoPrimeCorrection K.1 at h
    rw [hdegree] at h
    rw [h]
    unfold v15OdlyzkoArchLogA v15OdlyzkoArchLogB
    ring
  have hLogLower :
      (r : ℝ) * Real.log (36347 / 1000 : ℝ) +
        (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
        (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) <
      Real.log (((|K.discriminant| : ℤ) : ℝ)) := by
    rw [hLogD]
    linarith [hStrict, hZeros K]
  have hDpos : 0 < (((|K.discriminant| : ℤ) : ℝ)) := by
    have hz : K.discriminant ≠ 0 := NumberField.discr_ne_zero K.1
    exact_mod_cast (abs_pos.mpr hz : (0 : ℤ) < |K.discriminant|)
  have hExp := Real.exp_lt_exp.mpr hLogLower
  rw [Real.exp_log hDpos] at hExp
  have hTarget :
      Real.exp ((r : ℝ) * Real.log (36347 / 1000 : ℝ) +
        (c : ℝ) * Real.log (16593 / 1000 : ℝ) +
        (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ))) =
      (36347 / 1000 : ℝ) ^ r * (16593 / 1000 : ℝ) ^ c *
        Real.exp (v15OdlyzkoPrimeCorrection K.1 - (32 / 3 : ℝ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 36347 / 1000),
      Real.exp_log (by norm_num : (0 : ℝ) < 16593 / 1000)]
  rw [hTarget] at hExp
  exact hExp

/-- When the explicit formula supplies a summable enumeration of zero terms
inside the critical strip, the already proved `Phi` sign theorem discharges
the remaining zero-sign premise of the source-formula reduction. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_enumeratedZeros
    (zeros : CodedNumberField → ℕ → ℂ)
    (hStrip : ∀ K i, 0 ≤ (zeros K i).re ∧ (zeros K i).re ≤ 1)
    (hSummable : ∀ K, Summable (fun i ↦ v15OdlyzkoPhi (zeros K i)))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' i, v15OdlyzkoPhi (zeros K i)).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  apply v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula
    (fun K ↦ (∑' i, v15OdlyzkoPhi (zeros K i)).re) hFormula _ hAB
  intro K
  exact v15OdlyzkoPhi_zero_tsum_re_nonneg (zeros K) (hStrip K)
    (hSummable K)

end
end TraceEuclidean
