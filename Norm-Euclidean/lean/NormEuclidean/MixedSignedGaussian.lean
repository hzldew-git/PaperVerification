import NormEuclidean.SignedGaussianShape
import NormEuclidean.MixedGaussianFourier

/-!
# Signed Gaussian integrals in the fixed mixed trace coordinates

The actual signed test function is continuous, integrable, and has its
explicit Fourier transform under the unchanged trace Haar measure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace NormEuclidean.MixedSignedGaussian

open NumberField NumberField.mixedEmbedding MeasureTheory InfiniteTraceProduct
open SignedGaussianShape TraceGaussianFourier ArchimedeanTraceFourier
open scoped NumberField Classical NormEuclidean.InfiniteTraceHaar

variable (F : Type*) [Field F] [NumberField F]

def gaussian (a : RealPlace F → Fin 2) (t : ℝ) (x : mixedSpace F) : ℂ :=
  (polynomial F a x : ℂ) * MixedGaussianFourier.gaussian F t x

theorem trace_gaussian (a : RealPlace F → Fin 2) (t : ℝ) (x : mixedSpace F) :
    gaussian F a t x = SignedArchimedeanGaussian.gaussian F a t
      ((InfiniteTraceHaar.coordinates F).symm x) := by
  rw [SignedGaussianShape.gaussian_factor, ContinuousAddEquiv.apply_symm_apply,
    ← MixedGaussianFourier.trace_gaussian]
  rfl

theorem coordinates (a : RealPlace F → Fin 2) (t : ℝ) (x : InfiniteAdeleRing F) :
    gaussian F a t (InfiniteTraceHaar.coordinates F x) =
      SignedArchimedeanGaussian.gaussian F a t x := by
  rw [trace_gaussian, ContinuousAddEquiv.symm_apply_apply]

theorem continuous (a : RealPlace F → Fin 2) (t : ℝ) : Continuous (gaussian F a t) := by
  unfold gaussian polynomial MixedGaussianFourier.gaussian
  fun_prop

theorem norm_bound (a : RealPlace F → Fin 2) (t : ℝ) (x : mixedSpace F) :
    ‖gaussian F a t x‖ ≤ ‖IdealTheta.euclidean F x‖ ^ (∑ v, (a v).val) *
      Real.exp (-Real.pi * t * ‖IdealTheta.euclidean F x‖ ^ 2) := by
  have h := polynomial_bound F a 0 0 (by simp) x
  simp only [ArchimedeanLogScale.scale_zero, Real.exp_zero, one_pow, one_mul] at h
  simpa only [gaussian, MixedGaussianFourier.gaussian, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le] using
    mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

theorem separated (a : RealPlace F → Fin 2) (t : ℝ) (x : mixedSpace F) :
    gaussian F a t x =
      (∏ v, SignedRealGaussian.test (a v) (t : ℂ) (x.1 v)) *
        ∏ v : ComplexPlace F, complexGaussian t (x.2 v) := by
  rw [trace_gaussian, SignedArchimedeanGaussian.gaussian, InfiniteTraceFourier.tensor,
    ContinuousAddEquiv.apply_symm_apply]

theorem complex_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (complexGaussian t) complexHaar := by
  have hb : 0 < ((2 : ℂ) * Real.pi * t).re := by
    simpa using mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) ht
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : ℂ)
  have he : (fun z : ℂ ↦ Complex.exp (-((2 : ℂ) * Real.pi * t) * (‖z‖ : ℂ) ^ 2)) =
      complexGaussian t := by
    funext z
    unfold complexGaussian
    congr 1
    ring
  simp only [zero_mul, add_zero] at h
  rw [he] at h
  exact h.smul_measure (by norm_num)

theorem real_product_integrable (a : RealPlace F → Fin 2) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : RealPlace F → ℝ ↦
      ∏ v, SignedRealGaussian.test (a v) (t : ℂ) (x v)) := by
  apply Integrable.fintype_prod (μ := fun _ : RealPlace F ↦ (volume : Measure ℝ))
  intro v
  exact SignedRealGaussian.test_integrable (a v) (t : ℂ) (by simpa using ht)

theorem complex_product_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ComplexPlace F → ℂ ↦ ∏ v, complexGaussian t (x v))
      (complexProduct F) := by
  apply Integrable.fintype_prod (μ := fun _ : ComplexPlace F ↦ complexHaar)
  intro v
  exact complex_integrable t ht

theorem integrable (a : RealPlace F → Fin 2) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussian F a t) (InfiniteTraceHaar.mixedMeasure F) := by
  have h := (real_product_integrable F a t ht).mul_prod (complex_product_integrable F t ht)
  rw [mixed_product_eq] at h
  exact h.congr (Filter.Eventually.of_forall (fun x ↦ (separated F a t x).symm))

theorem fourier (a : RealPlace F → Fin 2) (t : ℝ) (ht : 0 < t) (z : mixedSpace F) :
    (∫ x : mixedSpace F, IdealTraceCharacters.frequency F z x * gaussian F a t x
      ∂InfiniteTraceHaar.mixedMeasure F) =
        SignedArchimedeanGaussian.scale F a t * gaussian F a t⁻¹ z := by
  have he := (InfiniteTraceHaar.coordinates_preserving F).integral_comp
    (InfiniteTraceHaar.coordinates F).toHomeomorph.measurableEmbedding
      (fun x ↦ IdealTraceCharacters.frequency F z x * gaussian F a t x)
  rw [← he]
  have hc (x : InfiniteAdeleRing F) :
      IdealTraceCharacters.frequency F z (InfiniteTraceHaar.coordinates F x) =
        AdelicTraceCharacter.infiniteCharacter
          (x * (InfiniteTraceHaar.coordinates F).symm z) := by
    simpa only [ContinuousAddEquiv.apply_symm_apply] using
      IdealTraceCharacters.frequency_coordinates F x ((InfiniteTraceHaar.coordinates F).symm z)
  simp_rw [hc, coordinates]
  rw [trace_gaussian]
  exact SignedArchimedeanGaussian.fourier F a t ht _

end NormEuclidean.MixedSignedGaussian
