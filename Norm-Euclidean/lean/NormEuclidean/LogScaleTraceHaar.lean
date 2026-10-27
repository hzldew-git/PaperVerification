import NormEuclidean.ArchimedeanLogScale
import NormEuclidean.MixedSignedGaussian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The actual logarithmic scaling of trace Haar measure

Both the real and complex dimensions are included in the Jacobian.
The negative trace Fourier character transforms by inverse scaling.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.LogScaleTraceHaar

open NumberField NumberField.mixedEmbedding InfiniteTraceProduct MeasureTheory
open ArchimedeanLogScale
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

/-- The logarithmic determinant, with real dimension two at each complex place. -/
def logJacobian (r : InfinitePlace F → ℝ) : ℝ :=
  (∑ v : RealPlace F, r v) + 2 * ∑ v : ComplexPlace F, r v

theorem determinant (r : InfinitePlace F → ℝ) :
    LinearMap.det (scale F r).toLinearMap = Real.exp (logJacobian F r) := by
  change LinearMap.det (LinearMap.prodMap
    (LinearMap.pi fun v : RealPlace F ↦
      (Real.exp (r v) • (1 : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj v))
    (LinearMap.pi fun v : ComplexPlace F ↦
      (Real.exp (r v) • (1 : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj v))) = _
  rw [LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_smul, Module.finrank_self, Complex.finrank_real_complex,
    map_one, mul_one, pow_one, ← Real.exp_nat_mul, ← Real.exp_sum]
  rw [← Real.exp_add]
  congr 1
  simp [logJacobian, Finset.mul_sum]

theorem map_measure (r : InfinitePlace F → ℝ) :
    Measure.map (scale F r) (InfiniteTraceHaar.mixedMeasure F) =
      ENNReal.ofReal (Real.exp (-logJacobian F r)) • InfiniteTraceHaar.mixedMeasure F := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (InfiniteTraceHaar.mixedMeasure F)
    (f := (scale F r).toLinearMap) (by rw [determinant]; exact Real.exp_ne_zero _)
  have he : ((scale F r).toLinearMap : mixedSpace F → mixedSpace F) = scale F r := rfl
  rw [he, determinant, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at h
  exact h

/-- Change of variables is computed for the fixed trace Haar measure. -/
theorem integral_comp (r : InfinitePlace F → ℝ) (f : mixedSpace F → ℂ) :
    (∫ x, f (scale F r x) ∂InfiniteTraceHaar.mixedMeasure F) =
      Real.exp (-logJacobian F r) • ∫ x, f x ∂InfiniteTraceHaar.mixedMeasure F := by
  have h := integral_map_equiv (μ := InfiniteTraceHaar.mixedMeasure F)
    (scale F r).toHomeomorph.toMeasurableEquiv f
  change (∫ x, f x ∂Measure.map (scale F r) (InfiniteTraceHaar.mixedMeasure F)) =
    (∫ x, f (scale F r x) ∂InfiniteTraceHaar.mixedMeasure F) at h
  rw [← h]
  rw [map_measure, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem integrable_comp (r : InfinitePlace F → ℝ) {f : mixedSpace F → ℂ}
    (hf : Integrable f (InfiniteTraceHaar.mixedMeasure F)) :
    Integrable (fun x ↦ f (scale F r x)) (InfiniteTraceHaar.mixedMeasure F) := by
  apply (integrable_map_equiv (scale F r).toHomeomorph.toMeasurableEquiv f).mp
  change Integrable f (Measure.map (scale F r) (InfiniteTraceHaar.mixedMeasure F))
  rw [map_measure]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem trace_pairing (r : InfinitePlace F → ℝ) (z x : mixedSpace F) :
    MixedTracePairing.form F z (scale F r x) =
      MixedTracePairing.form F (scale F r z) x := by
  simp only [MixedTracePairing.form_apply, scale_real, scale_complex]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    ring
  · apply Finset.sum_congr rfl
    intro v _
    simp only [Complex.real_smul]
    congr 2
    ring

theorem frequency (r : InfinitePlace F → ℝ) (z x : mixedSpace F) :
    IdealTraceCharacters.frequency F z (scale F r x) =
      IdealTraceCharacters.frequency F (scale F r z) x := by
  simp only [IdealTraceCharacters.frequency_apply, trace_pairing]

end NormEuclidean.LogScaleTraceHaar
