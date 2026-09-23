import TraceEuclidean.V15OdlyzkoZeroStrip
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Entire extension of the Odlyzko zero transform

The compactly supported nonnegative kernel defines a finite measure. Its
complex moment-generating function is entire and equals the exact transform
used in the explicit-formula reduction, after the central shift.
-/

namespace TraceEuclidean

noncomputable section
open MeasureTheory ProbabilityTheory

/-- The positive measure with density equal to the exact `b = 4` kernel. -/
def v15OdlyzkoKernelMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity (fun x : ℝ ↦ ENNReal.ofReal (v15OdlyzkoF4 x))

private theorem v15OdlyzkoKernelDensity_measurable :
    Measurable (fun x : ℝ ↦ ENNReal.ofReal (v15OdlyzkoF4 x)) :=
  v15OdlyzkoF4_continuous.measurable.ennreal_ofReal

private theorem v15OdlyzkoKernelDensity_lt_top :
    ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (v15OdlyzkoF4 x) < ⊤ :=
  Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- Every real exponential moment of the kernel measure is finite. -/
theorem v15OdlyzkoKernelMeasure_exp_integrable (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) v15OdlyzkoKernelMeasure := by
  rw [v15OdlyzkoKernelMeasure,
    integrable_withDensity_iff v15OdlyzkoKernelDensity_measurable
      v15OdlyzkoKernelDensity_lt_top]
  have hc : Continuous (fun x : ℝ ↦ v15OdlyzkoF4 x * Real.exp (t * x)) :=
    v15OdlyzkoF4_continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport
      (fun x : ℝ ↦ v15OdlyzkoF4 x * Real.exp (t * x)) :=
    v15OdlyzkoF4_hasCompactSupport.mul_right
  have hi : Integrable (fun x : ℝ ↦ v15OdlyzkoF4 x * Real.exp (t * x))
      (volume : Measure ℝ) := hc.integrable_of_hasCompactSupport hs
  have heq :
      (fun x : ℝ ↦ Real.exp (t * x) *
        (ENNReal.ofReal (v15OdlyzkoF4 x)).toReal) =
      (fun x : ℝ ↦ v15OdlyzkoF4 x * Real.exp (t * x)) := by
    funext x
    simp [ENNReal.toReal_ofReal (v15OdlyzkoF4_nonneg x), mul_comm]
  rw [heq]
  exact hi

private theorem v15OdlyzkoKernelMeasure_integrableExpSet :
    integrableExpSet id v15OdlyzkoKernelMeasure = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact v15OdlyzkoKernelMeasure_exp_integrable t

/-- The source-normalized transform is the complex moment-generating function
of the kernel measure, shifted by `1/2`. -/
theorem v15OdlyzkoPhi_eq_complexMGF (s : ℂ) :
    v15OdlyzkoPhi s =
      complexMGF id v15OdlyzkoKernelMeasure (s - (1 / 2 : ℂ)) := by
  rw [v15OdlyzkoPhi, complexMGF, v15OdlyzkoKernelMeasure,
    integral_withDensity_eq_integral_toReal_smul
      v15OdlyzkoKernelDensity_measurable v15OdlyzkoKernelDensity_lt_top]
  apply integral_congr_ae
  filter_upwards with x
  simp [ENNReal.toReal_ofReal (v15OdlyzkoF4_nonneg x)]

/-- The exact Odlyzko transform is holomorphic on all of `ℂ`. -/
theorem v15OdlyzkoPhi_differentiable : Differentiable ℂ v15OdlyzkoPhi := by
  have hMGF : Differentiable ℂ (complexMGF id v15OdlyzkoKernelMeasure) := by
    intro z
    have hz : z.re ∈ interior (integrableExpSet id v15OdlyzkoKernelMeasure) := by
      rw [v15OdlyzkoKernelMeasure_integrableExpSet]
      simp
    exact (hasDerivAt_complexMGF hz).differentiableAt
  have hshift : Differentiable ℂ (fun s : ℂ ↦ s - (1 / 2 : ℂ)) :=
    differentiable_id.sub (differentiable_const _)
  simpa only [Function.comp_def, ← v15OdlyzkoPhi_eq_complexMGF] using
    hMGF.comp hshift

/-- Differentiation under the exact source integral is valid at every complex
parameter; its derivative is the first exponential moment of the kernel. -/
theorem v15OdlyzkoPhi_hasDerivAt (s : ℂ) :
    HasDerivAt v15OdlyzkoPhi
      (∫ x : ℝ, (v15OdlyzkoF4 x : ℂ) * (x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))) s := by
  have hz : (s - (1 / 2 : ℂ)).re ∈
      interior (integrableExpSet id v15OdlyzkoKernelMeasure) := by
    rw [v15OdlyzkoKernelMeasure_integrableExpSet]
    simp
  have h := hasDerivAt_complexMGF (X := id)
    (μ := v15OdlyzkoKernelMeasure) hz
  have hshift : HasDerivAt (fun z : ℂ ↦ z - (1 / 2 : ℂ)) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
  have hcomp := h.comp s hshift
  have hmeasure :
      (∫ x : ℝ, (x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))
        ∂v15OdlyzkoKernelMeasure) =
      ∫ x : ℝ, (v15OdlyzkoF4 x : ℂ) * (x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) := by
    rw [v15OdlyzkoKernelMeasure,
      integral_withDensity_eq_integral_toReal_smul
        v15OdlyzkoKernelDensity_measurable v15OdlyzkoKernelDensity_lt_top]
    apply integral_congr_ae
    filter_upwards with x
    simp [ENNReal.toReal_ofReal (v15OdlyzkoF4_nonneg x)]
    ring
  have hfun : (fun z : ℂ ↦
      complexMGF id v15OdlyzkoKernelMeasure (z - (1 / 2 : ℂ))) =
      v15OdlyzkoPhi := by
    funext z
    exact (v15OdlyzkoPhi_eq_complexMGF z).symm
  simpa only [Function.comp_def, id_eq, mul_one, hfun, hmeasure] using hcomp

end
end TraceEuclidean
