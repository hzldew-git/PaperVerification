import NormEuclidean.AdelicTraceCharacter
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Real and complex trace-pairing Fourier normalization

The real trace pairing uses Lebesgue measure. For the complex trace
pairing `2 Re(xy)`, the actual Fourier integral uses twice planar
Lebesgue measure. The double transform is reflection under the usual
integrability and continuity hypotheses, so the factor two is proved
analytically rather than inferred from a desired quotient volume.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.ArchimedeanTraceFourier

open MeasureTheory MeasureTheory.Measure Complex ComplexConjugate
open scoped FourierTransform RealInnerProductSpace InnerProductSpace ENNReal

/-- The already constructed real-circle phase agrees with the standard Fourier character. -/
theorem phase_eq (t : ℝ) :
    AdelicTraceCharacter.realPhase (t : AddCircle (1 : ℝ)) = (Real.fourierChar t : ℂ) := by
  change (AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) = _
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, Real.fourierChar_apply]
  congr 2
  simp

/-- The real trace Fourier integral is the ordinary real Fourier transform. -/
theorem real_integral (f : ℝ → ℂ) (w : ℝ) :
    (∫ x : ℝ, AdelicTraceCharacter.realPhase (-(x * w) : AddCircle (1 : ℝ)) * f x) =
      𝓕 f w := by
  simp_rw [phase_eq]
  exact (Real.fourier_real_eq f w).symm

/-- Real Lebesgue measure is self-dual for the chosen negative trace character. -/
theorem real_double {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hc : Continuous f) (w : ℝ) : 𝓕 (𝓕 f) w = f (-w) := by
  have h := hf.fourierInv_fourier_eq hF (hc.continuousAt (x := -w))
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using h

/-- The complex additive trace Haar measure is twice planar Lebesgue measure. -/
def complexHaar : Measure ℂ := (2 : ℝ≥0∞) • volume

instance complexHaar_isHaar : IsAddHaarMeasure complexHaar :=
  IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)

/-- The actual complex Fourier integral with the negative trace character. -/
def complexFourier (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, (Real.fourierChar (-(2 * (z * w).re)) : ℂ) * f z ∂complexHaar

/-- The complex trace pairing is the ordinary real inner product after `2 conj`. -/
theorem inner_twist (z w : ℂ) : ⟪z, (2 : ℝ) • conj w⟫_ℝ = 2 * (z * w).re := by
  rw [inner_smul_right, Complex.inner]
  simp only [mul_re, conj_re, conj_im]
  ring

/-- Explicit change from the trace-pairing transform to the standard real-plane transform. -/
theorem complex_eq (f : ℂ → ℂ) (w : ℂ) :
    complexFourier f w = (2 : ℂ) * 𝓕 f ((2 : ℝ) • conj w) := by
  rw [complexFourier, complexHaar, integral_smul_measure]
  change (2 : ℂ) * _ = (2 : ℂ) * _
  congr 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with z
  rw [inner_twist]
  rfl

/-- The Jacobian of `z ↦ 2 conj z` is four in the real plane. -/
theorem integral_twist (g : ℂ → ℂ) :
    (∫ z : ℂ, g ((2 : ℝ) • conj z)) = (1 / 4 : ℂ) * ∫ z : ℂ, g z := by
  calc
    _ = ∫ z : ℂ, g ((2 : ℝ) • z) :=
      Complex.conjLIE.measurePreserving.integral_comp
        Complex.conjLIE.toHomeomorph.measurableEmbedding _
    _ = _ := by
      rw [Measure.integral_comp_smul volume g 2]
      norm_num [Complex.finrank_real_complex, real_smul]

/-- Double complex trace Fourier transformation is the standard double plane transform. -/
theorem complex_double_eq (f : ℂ → ℂ) (w : ℂ) :
    complexFourier (complexFourier f) w = 𝓕 (𝓕 f) w := by
  rw [complex_eq, Real.fourier_eq]
  simp_rw [complex_eq]
  let g : ℂ → ℂ := fun u ↦ (Real.fourierChar (-⟪u, w⟫_ℝ) : ℂ) * 𝓕 f u
  have hp (z : ℂ) :
      (Real.fourierChar (-⟪z, (2 : ℝ) • conj w⟫_ℝ) : ℂ) *
        ((2 : ℂ) * 𝓕 f ((2 : ℝ) • conj z)) = (2 : ℂ) * g ((2 : ℝ) • conj z) := by
    dsimp only [g]
    have he : ⟪z, (2 : ℝ) • conj w⟫_ℝ = ⟪(2 : ℝ) • conj z, w⟫_ℝ := by
      rw [inner_twist, inner_smul_left, Complex.inner]
      simp only [conj_conj, mul_comm w z, map_ofNat]
    rw [he]
    ring
  simp_rw [Circle.smul_def, smul_eq_mul, hp]
  rw [integral_const_mul, integral_twist]
  change (2 : ℂ) * (2 * ((1 / 4) * ∫ z : ℂ, g z)) = 𝓕 (𝓕 f) w
  rw [show (2 : ℂ) * (2 * ((1 / 4) * ∫ z : ℂ, g z)) = ∫ z : ℂ, g z by ring]
  rfl

/-- Twice planar Lebesgue measure is self-dual for the complex trace character. -/
theorem complex_double {f : ℂ → ℂ} (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hc : Continuous f) (w : ℂ) : complexFourier (complexFourier f) w = f (-w) := by
  rw [complex_double_eq]
  have h := hf.fourierInv_fourier_eq hF (hc.continuousAt (x := -w))
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using h

end NormEuclidean.ArchimedeanTraceFourier
