import TraceEuclidean.PoitouZeroStrip
import TraceEuclidean.OdlyzkoFourthRegularity
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace

/-- Every polynomial moment of the compactly supported source bump is
integrable.  This is the input used by `Real.contDiff_fourier`. -/
theorem poitouBumpComplex_moment_integrable (n : ℕ) :
    Integrable (fun x : ℝ ↦ ‖x‖ ^ n * ‖poitouBumpComplex x‖) volume := by
  apply poitouBumpComplex_integrable.norm.mono'
  · exact ((continuous_norm.comp continuous_id).pow n |>.mul
      (continuous_norm.comp poitouBumpComplex_continuous)).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : 1 ≤ |x|
    · rw [show poitouBumpComplex x = 0 by
        simp [poitouBumpComplex, poitouBump_eq_zero_of_one_le_abs hx]]
      simp
    · have hx' : ‖x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using le_of_not_ge hx
      have hp : ‖x‖ ^ n ≤ 1 := by
        simpa using pow_le_one₀ (norm_nonneg x) hx'
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) n)
          (norm_nonneg (poitouBumpComplex x)))]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hp (norm_nonneg (poitouBumpComplex x))

/-- The Fourier transform of the compactly supported source bump is `C⁴`. -/
theorem poitouBump_fourier_contDiff_four :
    ContDiff ℝ 4 (𝓕 poitouBumpComplex) := by
  apply Real.contDiff_fourier
  intro n hn
  exact poitouBumpComplex_moment_integrable n

/-- Poitou's Fourier amplitude is `C⁴`, including at its removable origin. -/
theorem poitouAmplitudeComplex_contDiff_four :
    ContDiff ℝ 4 poitouAmplitudeComplex := by
  have hcomp : ContDiff ℝ 4
      (fun x : ℝ ↦ 𝓕 poitouBumpComplex (x / (2 * Real.pi))) :=
    poitouBump_fourier_contDiff_four.comp
      (contDiff_id.div_const (2 * Real.pi))
  have heq : poitouAmplitudeComplex =
      (fun x : ℝ ↦ 𝓕 poitouBumpComplex (x / (2 * Real.pi))) := by
    funext x
    rw [poitouBump_fourier_eq_amplitude]
    change (poitouAmplitude x : ℂ) =
      (poitouAmplitude (2 * Real.pi * (x / (2 * Real.pi))) : ℂ)
    congr 2
    field_simp [Real.pi_ne_zero]
  rw [heq]
  exact hcomp

/-- The squared Poitou test function is `C⁴`. -/
theorem poitouTestComplex_contDiff_four :
    ContDiff ℝ 4 poitouTestComplex := by
  have hmul := poitouAmplitudeComplex_contDiff_four.mul
    poitouAmplitudeComplex_contDiff_four
  have heq : poitouTestComplex =
      (fun x : ℝ ↦ poitouAmplitudeComplex x * poitouAmplitudeComplex x) := by
    funext x
    simp [poitouTestComplex, poitouTest, poitouAmplitudeComplex, pow_two]
  rw [heq]
  exact hmul

/-- Scaling preserves the four derivatives needed for Fourier decay. -/
theorem poitouScaledTestComplex_contDiff_four (y : ℝ) :
    ContDiff ℝ 4 (poitouScaledTestComplex y) := by
  have h := poitouTestComplex_contDiff_four.comp
    (contDiff_const.mul contDiff_id :
      ContDiff ℝ 4 (fun x : ℝ ↦ Real.sqrt y * x))
  have heq : poitouScaledTestComplex y =
      (fun x : ℝ ↦ poitouTestComplex (Real.sqrt y * x)) := by
    funext x
    rfl
  rw [heq]
  exact h

/-- The hyperbolic-secant factor is `C⁴` as a complex-valued real function. -/
theorem poitouSechComplex_contDiff_four :
    ContDiff ℝ 4 TraceEuclidean.odlyzkoSechComplex := by
  have hReal : ContDiff ℝ 4 (fun x : ℝ ↦ 1 / Real.cosh (x / 2)) := by
    exact contDiff_const.div
      (Real.contDiff_cosh.comp (contDiff_id.div_const 2))
      (fun x ↦ (Real.cosh_pos (x / 2)).ne')
  change ContDiff ℝ 4 (fun x : ℝ ↦ ((1 / Real.cosh (x / 2) : ℝ) : ℂ))
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.comp hReal

/-- The full Poitou kernel `f(√y x) / cosh(x/2)` is `C⁴`. -/
theorem poitouFullKernelComplex_contDiff_four (y : ℝ) :
    ContDiff ℝ 4 (poitouFullKernelComplex y) := by
  have hmul := (poitouScaledTestComplex_contDiff_four y).mul
    poitouSechComplex_contDiff_four
  have heq : poitouFullKernelComplex y =
      (fun x : ℝ ↦ poitouScaledTestComplex y x *
        TraceEuclidean.odlyzkoSechComplex x) := by
    funext x
    simp only [poitouFullKernelComplex, poitouFullKernel, poitouScaledTestComplex,
      TraceEuclidean.odlyzkoSechComplex, TraceEuclidean.odlyzkoSech]
    push_cast
    field_simp [(Real.cosh_pos (x / 2)).ne']
  rw [heq]
  exact hmul

end

end TraceEuclidean.PoitouKernel
