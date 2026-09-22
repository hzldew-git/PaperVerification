import TraceEuclidean.V15OdlyzkoAutocorrelation
import Mathlib.Analysis.Fourier.Convolution

/-!
# Fourier positivity of Odlyzko's auxiliary function

Using the autocorrelation identity, this file proves that the Fourier
transform of `H` is one third of a real square.  The Fourier convention is
mathlib's `exp (-2 π i x w)` convention.  Consequently the transform is real
and nonnegative at every real frequency.
-/

namespace TraceEuclidean
noncomputable section
open MeasureTheory FourierTransform
open scoped Convolution

/-- The generating bump, viewed as a complex-valued integrable function. -/
def v15OdlyzkoBumpComplex (x : ℝ) : ℂ := v15OdlyzkoBump x

private theorem v15OdlyzkoBumpComplex_integrable : Integrable v15OdlyzkoBumpComplex volume := by
  exact v15OdlyzkoBump_integrable.ofReal

private theorem v15OdlyzkoBumpComplex_even (x : ℝ) :
    v15OdlyzkoBumpComplex (-x) = v15OdlyzkoBumpComplex x := by
  simp only [v15OdlyzkoBumpComplex, v15OdlyzkoBump_even]

private theorem v15OdlyzkoBumpComplex_fourier_real (w : ℝ) :
    𝓕 v15OdlyzkoBumpComplex w = ((𝓕 v15OdlyzkoBumpComplex w).re : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  calc
    (starRingEnd ℂ) (𝓕 v15OdlyzkoBumpComplex w) = 𝓕 v15OdlyzkoBumpComplex (-w) := by
      rw [Real.fourier_real_eq_integral_exp_smul,
        Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, map_mul, v15OdlyzkoBumpComplex, Complex.conj_ofReal,
        ← Complex.exp_conj, Complex.conj_I]
      congr 2
      push_cast
      ring
    _ = 𝓕 v15OdlyzkoBumpComplex w := by
      have hfun : v15OdlyzkoBumpComplex ∘ LinearIsometryEquiv.neg ℝ = v15OdlyzkoBumpComplex := by
        funext x
        exact v15OdlyzkoBumpComplex_even x
      have h := Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ) v15OdlyzkoBumpComplex w
      rw [hfun] at h
      simpa using h.symm

/-- Odlyzko's auxiliary function, viewed as a complex-valued function for its
Fourier transform. -/
def v15OdlyzkoHComplex (x : ℝ) : ℂ := v15OdlyzkoH x

private theorem v15OdlyzkoHComplex_eq_convolution (x : ℝ) :
    v15OdlyzkoHComplex x = (1 / 3 : ℂ) *
      (v15OdlyzkoBumpComplex ⋆[ContinuousLinearMap.mul ℂ ℂ] v15OdlyzkoBumpComplex) x := by
  have hreal := v15OdlyzkoH_eq_autocorrelation x
  unfold v15OdlyzkoHAutocorrelation at hreal
  rw [MeasureTheory.convolution_mul] at hreal
  unfold v15OdlyzkoHComplex
  rw [hreal, MeasureTheory.convolution_mul]
  simp_rw [v15OdlyzkoBumpComplex, ← Complex.ofReal_mul]
  have hIntegral :
      (∫ t : ℝ, ((v15OdlyzkoBump t * v15OdlyzkoBump (x - t) : ℝ) : ℂ)) =
        ((show ℝ from ∫ t : ℝ,
          v15OdlyzkoBump t * v15OdlyzkoBump (x - t)) : ℂ) :=
    integral_ofReal
  rw [hIntegral]
  push_cast
  ring

/-- The Fourier transform of `H` is one third of the square of the Fourier
transform of its generating bump. -/
theorem v15OdlyzkoH_fourier_eq_square (w : ℝ) :
    𝓕 v15OdlyzkoHComplex w = (1 / 3 : ℂ) * (𝓕 v15OdlyzkoBumpComplex w) ^ 2 := by
  let conv := v15OdlyzkoBumpComplex ⋆[ContinuousLinearMap.mul ℂ ℂ] v15OdlyzkoBumpComplex
  have hfun : v15OdlyzkoHComplex = fun x ↦ (1 / 3 : ℂ) * conv x := by
    funext x
    exact v15OdlyzkoHComplex_eq_convolution x
  have hscale : 𝓕 (fun x ↦ (1 / 3 : ℂ) * conv x) w =
      (1 / 3 : ℂ) * 𝓕 conv w := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq,
      ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Circle.smul_def]
    ring
  rw [hfun, hscale]
  change (1 / 3 : ℂ) * 𝓕 conv w = _
  dsimp only [conv]
  rw [Real.fourier_mul_convolution_eq v15OdlyzkoBumpComplex_integrable
    v15OdlyzkoBumpComplex_integrable]
  ring

/-- The Fourier transform of `H` has nonnegative real part at every real
frequency. -/
theorem v15OdlyzkoH_fourier_re_nonneg (w : ℝ) :
    0 ≤ (𝓕 v15OdlyzkoHComplex w).re := by
  rw [v15OdlyzkoH_fourier_eq_square, v15OdlyzkoBumpComplex_fourier_real]
  norm_num [pow_two]
  exact mul_self_nonneg _

/-- The Fourier transform of `H` is real at every real frequency. -/
theorem v15OdlyzkoH_fourier_im_eq_zero (w : ℝ) :
    (𝓕 v15OdlyzkoHComplex w).im = 0 := by
  rw [v15OdlyzkoH_fourier_eq_square, v15OdlyzkoBumpComplex_fourier_real]
  norm_num [pow_two]

end
end TraceEuclidean
