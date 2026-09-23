import TraceEuclidean.V15OdlyzkoDifferentiability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Elementary archimedean integral for Odlyzko's `b = 4` kernel

The table's exact error parameter is `8b/3`. This module derives the
`b = 4` value from the source kernel by an exact antiderivative, before
any of the harder strict numerical estimates for `A` and `B`.
-/

namespace TraceEuclidean

noncomputable section
open intervalIntegral

private def v15OdlyzkoHPrimitive (t : ℝ) : ℝ :=
  2 * t / 3 - t ^ 2 / 6 +
    (2 - t) * Real.sin (Real.pi * t) / (6 * Real.pi) -
    2 * Real.cos (Real.pi * t) / (3 * Real.pi ^ 2)

private theorem v15OdlyzkoHPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt v15OdlyzkoHPrimitive (v15OdlyzkoHCore t) t := by
  have harg : HasDerivAt (fun x : ℝ ↦ Real.pi * x) Real.pi t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul Real.pi
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (Real.pi * x))
      (Real.cos (Real.pi * t) * Real.pi) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (Real.pi * t)).comp t harg
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (Real.pi * x))
      (-Real.sin (Real.pi * t) * Real.pi) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (Real.pi * t)).comp t harg
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 - x) (-1) t := by
    convert (hasDerivAt_const t 2).sub (hasDerivAt_id t) using 1
    all_goals first | rfl | norm_num
  have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1
    all_goals first | rfl | (simp only [id_eq]; ring)
  unfold v15OdlyzkoHPrimitive
  convert (((((hasDerivAt_id t).const_mul 2).div_const 3).sub
    (hsq.div_const 6)).add
    ((hlin.mul hsin).div_const (6 * Real.pi))).sub
    ((hcos.const_mul 2).div_const (3 * Real.pi ^ 2)) using 1
  all_goals first
    | rfl
    | (unfold v15OdlyzkoHCore; field_simp [Real.pi_ne_zero]; ring)

/-- The exact area under Odlyzko's auxiliary function on its positive support. -/
theorem v15OdlyzkoHCore_intervalIntegral_zero_two :
    ∫ t in (0 : ℝ)..2, v15OdlyzkoHCore t = 2 / 3 := by
  have hint : IntervalIntegrable v15OdlyzkoHCore MeasureTheory.volume 0 2 :=
    v15OdlyzkoHCore_continuous.intervalIntegrable 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ v15OdlyzkoHPrimitive_hasDerivAt t) hint]
  unfold v15OdlyzkoHPrimitive
  rw [show Real.pi * (2 : ℝ) = 2 * Real.pi by ring,
    Real.sin_two_pi, Real.cos_two_pi]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [Real.pi_ne_zero]
  ring

/-- Scaling to the `b = 4` row gives the exact positive-support area. -/
theorem v15OdlyzkoH4_intervalIntegral_zero_eight :
    ∫ x in (0 : ℝ)..8, v15OdlyzkoH (x / 4) = 8 / 3 := by
  have hcore :
      (∫ x in (0 : ℝ)..2, v15OdlyzkoH x) =
        ∫ x in (0 : ℝ)..2, v15OdlyzkoHCore x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx₀ : 0 ≤ x := (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2) ▸ hx).1
    have hx₂ : x ≤ 2 := (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2) ▸ hx).2
    simp [v15OdlyzkoH, abs_of_nonneg hx₀, hx₂]
  rw [intervalIntegral.integral_comp_div v15OdlyzkoH (by norm_num : (4 : ℝ) ≠ 0)]
  norm_num [smul_eq_mul, hcore, v15OdlyzkoHCore_intervalIntegral_zero_two]

/-- The exact archimedean error integral behind Table 4 has value `32/3`.
The factor `4` is the coefficient in the source explicit formula. -/
theorem v15OdlyzkoF4_archimedean_error_integral :
    4 * (∫ x in Set.Ioi (0 : ℝ),
      v15OdlyzkoF4 x * Real.cosh (x / 2)) = 32 / 3 := by
  have hpoint (x : ℝ) :
      v15OdlyzkoF4 x * Real.cosh (x / 2) = v15OdlyzkoH (x / 4) := by
    unfold v15OdlyzkoF4
    field_simp [(Real.cosh_pos (x / 2)).ne']
  have hcont : Continuous (fun x : ℝ ↦
      v15OdlyzkoF4 x * Real.cosh (x / 2)) :=
    v15OdlyzkoF4_continuous.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hcompact : HasCompactSupport (fun x : ℝ ↦
      v15OdlyzkoF4 x * Real.cosh (x / 2)) :=
    v15OdlyzkoF4_hasCompactSupport.mul_right
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ ↦
      v15OdlyzkoF4 x * Real.cosh (x / 2)) (Set.Ioi 0) :=
    (hcont.integrable_of_hasCompactSupport hcompact).integrableOn
  have htail :
      (∫ x in Set.Ioi (8 : ℝ),
        v15OdlyzkoF4 x * Real.cosh (x / 2)) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    change 8 < x at hx
    have hxabs : 8 < |x| := by
      rw [abs_of_pos (by linarith [hx] : 0 < x)]
      exact hx
    rw [v15OdlyzkoF4_eq_zero_of_eight_lt_abs hxabs, zero_mul]
  have hinterval :
      (∫ x in (0 : ℝ)..8, v15OdlyzkoF4 x * Real.cosh (x / 2)) = 8 / 3 := by
    calc
      (∫ x in (0 : ℝ)..8, v15OdlyzkoF4 x * Real.cosh (x / 2)) =
          ∫ x in (0 : ℝ)..8, v15OdlyzkoH (x / 4) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hpoint x
      _ = 8 / 3 := v15OdlyzkoH4_intervalIntegral_zero_eight
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hint
    (by norm_num : (0 : ℝ) ≤ 8)
  rw [htail, sub_zero, hinterval] at hsplit
  norm_num [hsplit]

end
end TraceEuclidean
