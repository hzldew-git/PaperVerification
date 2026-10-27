import NormEuclidean.IdealGaussianPeriodization
import NormEuclidean.IdealTraceCharacters

/-!
# Actual mixed-space Gaussian Fourier integrals

The fixed infinite adelic Gaussian and trace Haar measure are carried
to the original mixed coordinates. Its integrability and Fourier
integral are proved from the existing actual adelic calculation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.MixedGaussianFourier

open NumberField NumberField.mixedEmbedding MeasureTheory
open scoped NumberField Classical NormEuclidean.InfiniteTraceHaar

variable (F : Type*) [Field F] [NumberField F]

/-- The original trace Gaussian in the original mixed space. -/
def gaussian (t : ℝ) (x : mixedSpace F) : ℂ :=
  (Real.exp (-Real.pi * t * ‖IdealTheta.euclidean F x‖ ^ 2) : ℂ)

/-- Mixed evaluation agrees with the unchanged original infinite adelic Gaussian. -/
theorem trace_gaussian (t : ℝ) (x : mixedSpace F) :
    gaussian F t x = TraceGaussianFourier.gaussian F t
      ((InfiniteTraceHaar.coordinates F).symm x) := by
  simpa only [gaussian, map_zero, add_zero] using
    (IdealGaussianPeriodization.gaussian_translate F t x 0).symm

/-- The actual coordinate transport retains the original Gaussian values. -/
theorem coordinates (t : ℝ) (a : InfiniteAdeleRing F) :
    gaussian F t (InfiniteTraceHaar.coordinates F a) =
      TraceGaussianFourier.gaussian F t a := by
  rw [trace_gaussian, ContinuousAddEquiv.symm_apply_apply]

/-- The actual mixed Gaussian is continuous, including at zero. -/
theorem continuous (t : ℝ) : Continuous (gaussian F t) := by
  unfold gaussian
  fun_prop

/-- The original trace Haar integral has exactly the existing degree-over-two scale. -/
theorem integral (t : ℝ) (ht : 0 < t) :
    (∫ x : mixedSpace F, gaussian F t x ∂InfiniteTraceHaar.mixedMeasure F) =
      (t : ℂ) ^ (-((Module.finrank ℚ F : ℂ) / 2)) := by
  have he := (InfiniteTraceHaar.coordinates_preserving F).integral_comp
    (InfiniteTraceHaar.coordinates F).toHomeomorph.measurableEmbedding (gaussian F t)
  rw [← he]
  simp_rw [coordinates]
  exact TraceGaussianFourier.integral_gaussian F t ht

/-- Integrability follows from the proved nonzero integral, rather than an analytic premise. -/
theorem integrable (t : ℝ) (ht : 0 < t) :
    Integrable (gaussian F t) (InfiniteTraceHaar.mixedMeasure F) := by
  apply MeasureTheory.Integrable.of_integral_ne_zero
  rw [integral F t ht]
  exact (Complex.cpow_ne_zero_iff).mpr (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))

/-- The mixed-space actual trace-character Fourier integral is the reciprocal Gaussian. -/
theorem fourier (t : ℝ) (ht : 0 < t) (z : mixedSpace F) :
    (∫ x : mixedSpace F, IdealTraceCharacters.frequency F z x * gaussian F t x
        ∂InfiniteTraceHaar.mixedMeasure F) =
      (t : ℂ) ^ (-((Module.finrank ℚ F : ℂ) / 2)) * gaussian F t⁻¹ z := by
  have he := (InfiniteTraceHaar.coordinates_preserving F).integral_comp
    (InfiniteTraceHaar.coordinates F).toHomeomorph.measurableEmbedding
      (fun x ↦ IdealTraceCharacters.frequency F z x * gaussian F t x)
  rw [← he]
  have hc (a : InfiniteAdeleRing F) :
      IdealTraceCharacters.frequency F z (InfiniteTraceHaar.coordinates F a) =
        AdelicTraceCharacter.infiniteCharacter
          (a * (InfiniteTraceHaar.coordinates F).symm z) := by
    simpa only [ContinuousAddEquiv.apply_symm_apply] using
      IdealTraceCharacters.frequency_coordinates F a ((InfiniteTraceHaar.coordinates F).symm z)
  simp_rw [hc, coordinates]
  rw [trace_gaussian]
  exact TraceGaussianFourier.fourier_gaussian_degree F t ht _

end NormEuclidean.MixedGaussianFourier
