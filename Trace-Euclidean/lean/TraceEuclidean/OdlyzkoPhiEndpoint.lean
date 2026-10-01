import TraceEuclidean.OdlyzkoPhiSymmetry
import TraceEuclidean.OdlyzkoArchimedean

/-!
# Exact endpoint values of Odlyzko's zero transform

The source's archimedean error integral is also the contribution of the two
endpoint transforms in the explicit formula.  This module derives their exact
values from the same `b = 4` test function.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory

private def odlyzkoErrorIntegrand (x : ℝ) : ℝ :=
  odlyzkoF4 x * Real.cosh (x / 2)

private theorem odlyzkoErrorIntegrand_even (x : ℝ) :
    odlyzkoErrorIntegrand (-x) = odlyzkoErrorIntegrand x := by
  rw [odlyzkoErrorIntegrand, odlyzkoErrorIntegrand,
    odlyzkoF4_even, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

private theorem odlyzkoErrorIntegrand_abs (x : ℝ) :
    odlyzkoErrorIntegrand |x| = odlyzkoErrorIntegrand x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    exact odlyzkoErrorIntegrand_even x

private theorem odlyzkoErrorIntegrand_integral :
    (∫ x : ℝ, odlyzkoErrorIntegrand x) = 16 / 3 := by
  have hhalf :
      (∫ x in Set.Ioi (0 : ℝ), odlyzkoErrorIntegrand x) = 8 / 3 := by
    have h := odlyzkoF4_archimedean_error_integral
    change 4 * (∫ x in Set.Ioi (0 : ℝ), odlyzkoErrorIntegrand x) = 32 / 3 at h
    linarith
  calc
    (∫ x : ℝ, odlyzkoErrorIntegrand x) =
        ∫ x : ℝ, odlyzkoErrorIntegrand |x| := by
      apply integral_congr_ae
      filter_upwards with x
      exact (odlyzkoErrorIntegrand_abs x).symm
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), odlyzkoErrorIntegrand x :=
      integral_comp_abs
    _ = 16 / 3 := by rw [hhalf]; ring

private def odlyzkoPositiveEndpoint (x : ℝ) : ℝ :=
  odlyzkoF4 x * Real.exp (x / 2)

private def odlyzkoNegativeEndpoint (x : ℝ) : ℝ :=
  odlyzkoF4 x * Real.exp (-x / 2)

private theorem odlyzkoPositiveEndpoint_integrable :
    Integrable odlyzkoPositiveEndpoint volume := by
  apply (odlyzkoF4_continuous.mul
    (Real.continuous_exp.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
  exact odlyzkoF4_hasCompactSupport.mul_right

private theorem odlyzkoNegativeEndpoint_integrable :
    Integrable odlyzkoNegativeEndpoint volume := by
  apply (odlyzkoF4_continuous.mul
    (Real.continuous_exp.comp (continuous_neg.div_const 2))).integrable_of_hasCompactSupport
  exact odlyzkoF4_hasCompactSupport.mul_right

private theorem odlyzkoEndpoints_integrals_eq :
    (∫ x : ℝ, odlyzkoPositiveEndpoint x) =
      ∫ x : ℝ, odlyzkoNegativeEndpoint x := by
  calc
    (∫ x : ℝ, odlyzkoPositiveEndpoint x) =
        ∫ x : ℝ, odlyzkoPositiveEndpoint (-x) :=
      (integral_neg_eq_self odlyzkoPositiveEndpoint volume).symm
    _ = ∫ x : ℝ, odlyzkoNegativeEndpoint x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [odlyzkoPositiveEndpoint, odlyzkoNegativeEndpoint,
        odlyzkoF4_even]

private theorem odlyzkoPositiveEndpoint_integral :
    (∫ x : ℝ, odlyzkoPositiveEndpoint x) = 16 / 3 := by
  have hpoint (x : ℝ) :
      2 * odlyzkoErrorIntegrand x =
        odlyzkoPositiveEndpoint x + odlyzkoNegativeEndpoint x := by
    unfold odlyzkoErrorIntegrand odlyzkoPositiveEndpoint
      odlyzkoNegativeEndpoint
    rw [Real.cosh_eq]
    ring
  have hsum :
      2 * (∫ x : ℝ, odlyzkoErrorIntegrand x) =
        (∫ x : ℝ, odlyzkoPositiveEndpoint x) +
          (∫ x : ℝ, odlyzkoNegativeEndpoint x) := by
    calc
      2 * (∫ x : ℝ, odlyzkoErrorIntegrand x) =
          ∫ x : ℝ, 2 * odlyzkoErrorIntegrand x := by
        rw [integral_const_mul]
      _ = ∫ x : ℝ,
          odlyzkoPositiveEndpoint x + odlyzkoNegativeEndpoint x := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = _ := integral_add odlyzkoPositiveEndpoint_integrable
        odlyzkoNegativeEndpoint_integrable
  rw [← odlyzkoEndpoints_integrals_eq,
    odlyzkoErrorIntegrand_integral] at hsum
  linarith

private theorem odlyzkoPhi_one_eq_positiveEndpoint :
    odlyzkoPhi 1 =
      (∫ x : ℝ, odlyzkoPositiveEndpoint x : ℝ) := by
  unfold odlyzkoPhi
  calc
    (∫ x : ℝ, (odlyzkoF4 x : ℂ) *
      Complex.exp (((1 : ℂ) - 1 / 2) * (x : ℂ))) =
        ∫ x : ℝ, (odlyzkoPositiveEndpoint x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have harg : ((1 : ℂ) - 1 / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, (Complex.ofReal_exp (x / 2)).symm]
      simp [odlyzkoPositiveEndpoint]
    _ = _ := integral_ofReal

/-- The endpoint transform at `s = 1` is the exact real value `16/3`. -/
theorem odlyzkoPhi_one : odlyzkoPhi 1 = 16 / 3 := by
  rw [odlyzkoPhi_one_eq_positiveEndpoint,
    odlyzkoPositiveEndpoint_integral]
  norm_num

/-- Reflection symmetry gives the other endpoint value. -/
theorem odlyzkoPhi_zero : odlyzkoPhi 0 = 16 / 3 := by
  simpa using (odlyzkoPhi_one_sub (1 : ℂ)).trans odlyzkoPhi_one

/-- The sum of the two endpoint terms equals Odlyzko's exact error `E = 32/3`. -/
theorem odlyzkoPhi_zero_add_one :
    odlyzkoPhi 0 + odlyzkoPhi 1 = 32 / 3 := by
  rw [odlyzkoPhi_zero, odlyzkoPhi_one]
  ring

end
end TraceEuclidean
