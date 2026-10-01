import TraceEuclidean.OdlyzkoZeroStrip
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
def odlyzkoKernelMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity (fun x : ℝ ↦ ENNReal.ofReal (odlyzkoF4 x))

private theorem odlyzkoKernelDensity_measurable :
    Measurable (fun x : ℝ ↦ ENNReal.ofReal (odlyzkoF4 x)) :=
  odlyzkoF4_continuous.measurable.ennreal_ofReal

private theorem odlyzkoKernelDensity_lt_top :
    ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (odlyzkoF4 x) < ⊤ :=
  Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- Every real exponential moment of the kernel measure is finite. -/
theorem odlyzkoKernelMeasure_exp_integrable (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) odlyzkoKernelMeasure := by
  rw [odlyzkoKernelMeasure,
    integrable_withDensity_iff odlyzkoKernelDensity_measurable
      odlyzkoKernelDensity_lt_top]
  have hc : Continuous (fun x : ℝ ↦ odlyzkoF4 x * Real.exp (t * x)) :=
    odlyzkoF4_continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport
      (fun x : ℝ ↦ odlyzkoF4 x * Real.exp (t * x)) :=
    odlyzkoF4_hasCompactSupport.mul_right
  have hi : Integrable (fun x : ℝ ↦ odlyzkoF4 x * Real.exp (t * x))
      (volume : Measure ℝ) := hc.integrable_of_hasCompactSupport hs
  have heq :
      (fun x : ℝ ↦ Real.exp (t * x) *
        (ENNReal.ofReal (odlyzkoF4 x)).toReal) =
      (fun x : ℝ ↦ odlyzkoF4 x * Real.exp (t * x)) := by
    funext x
    simp [ENNReal.toReal_ofReal (odlyzkoF4_nonneg x), mul_comm]
  rw [heq]
  exact hi

private theorem odlyzkoKernelMeasure_integrableExpSet :
    integrableExpSet id odlyzkoKernelMeasure = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact odlyzkoKernelMeasure_exp_integrable t

/-- The source-normalized transform is the complex moment-generating function
of the kernel measure, shifted by `1/2`. -/
theorem odlyzkoPhi_eq_complexMGF (s : ℂ) :
    odlyzkoPhi s =
      complexMGF id odlyzkoKernelMeasure (s - (1 / 2 : ℂ)) := by
  rw [odlyzkoPhi, complexMGF, odlyzkoKernelMeasure,
    integral_withDensity_eq_integral_toReal_smul
      odlyzkoKernelDensity_measurable odlyzkoKernelDensity_lt_top]
  apply integral_congr_ae
  filter_upwards with x
  simp [ENNReal.toReal_ofReal (odlyzkoF4_nonneg x)]

/-- The exact Odlyzko transform is holomorphic on all of `ℂ`. -/
theorem odlyzkoPhi_differentiable : Differentiable ℂ odlyzkoPhi := by
  have hMGF : Differentiable ℂ (complexMGF id odlyzkoKernelMeasure) := by
    intro z
    have hz : z.re ∈ interior (integrableExpSet id odlyzkoKernelMeasure) := by
      rw [odlyzkoKernelMeasure_integrableExpSet]
      simp
    exact (hasDerivAt_complexMGF hz).differentiableAt
  have hshift : Differentiable ℂ (fun s : ℂ ↦ s - (1 / 2 : ℂ)) :=
    differentiable_id.sub (differentiable_const _)
  simpa only [Function.comp_def, ← odlyzkoPhi_eq_complexMGF] using
    hMGF.comp hshift

/-- Differentiation under the exact source integral is valid at every complex
parameter; its derivative is the first exponential moment of the kernel. -/
theorem odlyzkoPhi_hasDerivAt (s : ℂ) :
    HasDerivAt odlyzkoPhi
      (∫ x : ℝ, (odlyzkoF4 x : ℂ) * (x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))) s := by
  have hz : (s - (1 / 2 : ℂ)).re ∈
      interior (integrableExpSet id odlyzkoKernelMeasure) := by
    rw [odlyzkoKernelMeasure_integrableExpSet]
    simp
  have h := hasDerivAt_complexMGF (X := id)
    (μ := odlyzkoKernelMeasure) hz
  have hshift : HasDerivAt (fun z : ℂ ↦ z - (1 / 2 : ℂ)) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
  have hcomp := h.comp s hshift
  have hmeasure :
      (∫ x : ℝ, (x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))
        ∂odlyzkoKernelMeasure) =
      ∫ x : ℝ, (odlyzkoF4 x : ℂ) * (x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) := by
    rw [odlyzkoKernelMeasure,
      integral_withDensity_eq_integral_toReal_smul
        odlyzkoKernelDensity_measurable odlyzkoKernelDensity_lt_top]
    apply integral_congr_ae
    filter_upwards with x
    simp [ENNReal.toReal_ofReal (odlyzkoF4_nonneg x)]
    ring
  have hfun : (fun z : ℂ ↦
      complexMGF id odlyzkoKernelMeasure (z - (1 / 2 : ℂ))) =
      odlyzkoPhi := by
    funext z
    exact (odlyzkoPhi_eq_complexMGF z).symm
  simpa only [Function.comp_def, id_eq, mul_one, hfun, hmeasure] using hcomp

end
end TraceEuclidean
