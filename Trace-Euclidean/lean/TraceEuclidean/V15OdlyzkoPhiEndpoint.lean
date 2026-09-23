import TraceEuclidean.V15OdlyzkoPhiSymmetry
import TraceEuclidean.V15OdlyzkoArchimedean

/-!
# Exact endpoint values of Odlyzko's zero transform

The source's archimedean error integral is also the contribution of the two
endpoint transforms in the explicit formula.  This module derives their exact
values from the same `b = 4` test function.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory

private def v15OdlyzkoErrorIntegrand (x : ℝ) : ℝ :=
  v15OdlyzkoF4 x * Real.cosh (x / 2)

private theorem v15OdlyzkoErrorIntegrand_even (x : ℝ) :
    v15OdlyzkoErrorIntegrand (-x) = v15OdlyzkoErrorIntegrand x := by
  rw [v15OdlyzkoErrorIntegrand, v15OdlyzkoErrorIntegrand,
    v15OdlyzkoF4_even, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

private theorem v15OdlyzkoErrorIntegrand_abs (x : ℝ) :
    v15OdlyzkoErrorIntegrand |x| = v15OdlyzkoErrorIntegrand x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    exact v15OdlyzkoErrorIntegrand_even x

private theorem v15OdlyzkoErrorIntegrand_integral :
    (∫ x : ℝ, v15OdlyzkoErrorIntegrand x) = 16 / 3 := by
  have hhalf :
      (∫ x in Set.Ioi (0 : ℝ), v15OdlyzkoErrorIntegrand x) = 8 / 3 := by
    have h := v15OdlyzkoF4_archimedean_error_integral
    change 4 * (∫ x in Set.Ioi (0 : ℝ), v15OdlyzkoErrorIntegrand x) = 32 / 3 at h
    linarith
  calc
    (∫ x : ℝ, v15OdlyzkoErrorIntegrand x) =
        ∫ x : ℝ, v15OdlyzkoErrorIntegrand |x| := by
      apply integral_congr_ae
      filter_upwards with x
      exact (v15OdlyzkoErrorIntegrand_abs x).symm
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), v15OdlyzkoErrorIntegrand x :=
      integral_comp_abs
    _ = 16 / 3 := by rw [hhalf]; ring

private def v15OdlyzkoPositiveEndpoint (x : ℝ) : ℝ :=
  v15OdlyzkoF4 x * Real.exp (x / 2)

private def v15OdlyzkoNegativeEndpoint (x : ℝ) : ℝ :=
  v15OdlyzkoF4 x * Real.exp (-x / 2)

private theorem v15OdlyzkoPositiveEndpoint_integrable :
    Integrable v15OdlyzkoPositiveEndpoint volume := by
  apply (v15OdlyzkoF4_continuous.mul
    (Real.continuous_exp.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
  exact v15OdlyzkoF4_hasCompactSupport.mul_right

private theorem v15OdlyzkoNegativeEndpoint_integrable :
    Integrable v15OdlyzkoNegativeEndpoint volume := by
  apply (v15OdlyzkoF4_continuous.mul
    (Real.continuous_exp.comp (continuous_neg.div_const 2))).integrable_of_hasCompactSupport
  exact v15OdlyzkoF4_hasCompactSupport.mul_right

private theorem v15OdlyzkoEndpoints_integrals_eq :
    (∫ x : ℝ, v15OdlyzkoPositiveEndpoint x) =
      ∫ x : ℝ, v15OdlyzkoNegativeEndpoint x := by
  calc
    (∫ x : ℝ, v15OdlyzkoPositiveEndpoint x) =
        ∫ x : ℝ, v15OdlyzkoPositiveEndpoint (-x) :=
      (integral_neg_eq_self v15OdlyzkoPositiveEndpoint volume).symm
    _ = ∫ x : ℝ, v15OdlyzkoNegativeEndpoint x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [v15OdlyzkoPositiveEndpoint, v15OdlyzkoNegativeEndpoint,
        v15OdlyzkoF4_even]

private theorem v15OdlyzkoPositiveEndpoint_integral :
    (∫ x : ℝ, v15OdlyzkoPositiveEndpoint x) = 16 / 3 := by
  have hpoint (x : ℝ) :
      2 * v15OdlyzkoErrorIntegrand x =
        v15OdlyzkoPositiveEndpoint x + v15OdlyzkoNegativeEndpoint x := by
    unfold v15OdlyzkoErrorIntegrand v15OdlyzkoPositiveEndpoint
      v15OdlyzkoNegativeEndpoint
    rw [Real.cosh_eq]
    ring
  have hsum :
      2 * (∫ x : ℝ, v15OdlyzkoErrorIntegrand x) =
        (∫ x : ℝ, v15OdlyzkoPositiveEndpoint x) +
          (∫ x : ℝ, v15OdlyzkoNegativeEndpoint x) := by
    calc
      2 * (∫ x : ℝ, v15OdlyzkoErrorIntegrand x) =
          ∫ x : ℝ, 2 * v15OdlyzkoErrorIntegrand x := by
        rw [integral_const_mul]
      _ = ∫ x : ℝ,
          v15OdlyzkoPositiveEndpoint x + v15OdlyzkoNegativeEndpoint x := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = _ := integral_add v15OdlyzkoPositiveEndpoint_integrable
        v15OdlyzkoNegativeEndpoint_integrable
  rw [← v15OdlyzkoEndpoints_integrals_eq,
    v15OdlyzkoErrorIntegrand_integral] at hsum
  linarith

private theorem v15OdlyzkoPhi_one_eq_positiveEndpoint :
    v15OdlyzkoPhi 1 =
      (∫ x : ℝ, v15OdlyzkoPositiveEndpoint x : ℝ) := by
  unfold v15OdlyzkoPhi
  calc
    (∫ x : ℝ, (v15OdlyzkoF4 x : ℂ) *
      Complex.exp (((1 : ℂ) - 1 / 2) * (x : ℂ))) =
        ∫ x : ℝ, (v15OdlyzkoPositiveEndpoint x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have harg : ((1 : ℂ) - 1 / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, (Complex.ofReal_exp (x / 2)).symm]
      simp [v15OdlyzkoPositiveEndpoint]
    _ = _ := integral_ofReal

/-- The endpoint transform at `s = 1` is the exact real value `16/3`. -/
theorem v15OdlyzkoPhi_one : v15OdlyzkoPhi 1 = 16 / 3 := by
  rw [v15OdlyzkoPhi_one_eq_positiveEndpoint,
    v15OdlyzkoPositiveEndpoint_integral]
  norm_num

/-- Reflection symmetry gives the other endpoint value. -/
theorem v15OdlyzkoPhi_zero : v15OdlyzkoPhi 0 = 16 / 3 := by
  simpa using (v15OdlyzkoPhi_one_sub (1 : ℂ)).trans v15OdlyzkoPhi_one

/-- The sum of the two endpoint terms equals Odlyzko's exact error `E = 32/3`. -/
theorem v15OdlyzkoPhi_zero_add_one :
    v15OdlyzkoPhi 0 + v15OdlyzkoPhi 1 = 32 / 3 := by
  rw [v15OdlyzkoPhi_zero, v15OdlyzkoPhi_one]
  ring

end
end TraceEuclidean
