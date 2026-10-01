import TraceEuclidean.OdlyzkoAutocorrelation
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
def odlyzkoBumpComplex (x : ℝ) : ℂ := odlyzkoBump x

private theorem odlyzkoBumpComplex_integrable : Integrable odlyzkoBumpComplex volume := by
  exact odlyzkoBump_integrable.ofReal

private theorem odlyzkoBumpComplex_even (x : ℝ) :
    odlyzkoBumpComplex (-x) = odlyzkoBumpComplex x := by
  simp only [odlyzkoBumpComplex, odlyzkoBump_even]

private theorem odlyzkoBumpComplex_fourier_real (w : ℝ) :
    𝓕 odlyzkoBumpComplex w = ((𝓕 odlyzkoBumpComplex w).re : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  calc
    (starRingEnd ℂ) (𝓕 odlyzkoBumpComplex w) = 𝓕 odlyzkoBumpComplex (-w) := by
      rw [Real.fourier_real_eq_integral_exp_smul,
        Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, map_mul, odlyzkoBumpComplex, Complex.conj_ofReal,
        ← Complex.exp_conj, Complex.conj_I]
      congr 2
      push_cast
      ring
    _ = 𝓕 odlyzkoBumpComplex w := by
      have hfun : odlyzkoBumpComplex ∘ LinearIsometryEquiv.neg ℝ = odlyzkoBumpComplex := by
        funext x
        exact odlyzkoBumpComplex_even x
      have h := Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ) odlyzkoBumpComplex w
      rw [hfun] at h
      simpa using h.symm

/-- Odlyzko's auxiliary function, viewed as a complex-valued function for its
Fourier transform. -/
def odlyzkoHComplex (x : ℝ) : ℂ := odlyzkoH x

/-- The complex-valued auxiliary function is integrable. -/
theorem odlyzkoHComplex_integrable : Integrable odlyzkoHComplex volume := by
  exact odlyzkoH_integrable.ofReal

private theorem odlyzkoHComplex_eq_convolution (x : ℝ) :
    odlyzkoHComplex x = (1 / 3 : ℂ) *
      (odlyzkoBumpComplex ⋆[ContinuousLinearMap.mul ℂ ℂ] odlyzkoBumpComplex) x := by
  have hreal := odlyzkoH_eq_autocorrelation x
  unfold odlyzkoHAutocorrelation at hreal
  rw [MeasureTheory.convolution_mul] at hreal
  unfold odlyzkoHComplex
  rw [hreal, MeasureTheory.convolution_mul]
  simp_rw [odlyzkoBumpComplex, ← Complex.ofReal_mul]
  have hIntegral :
      (∫ t : ℝ, ((odlyzkoBump t * odlyzkoBump (x - t) : ℝ) : ℂ)) =
        ((show ℝ from ∫ t : ℝ,
          odlyzkoBump t * odlyzkoBump (x - t)) : ℂ) :=
    integral_ofReal
  rw [hIntegral]
  push_cast
  ring

/-- The Fourier transform of `H` is one third of the square of the Fourier
transform of its generating bump. -/
theorem odlyzkoH_fourier_eq_square (w : ℝ) :
    𝓕 odlyzkoHComplex w = (1 / 3 : ℂ) * (𝓕 odlyzkoBumpComplex w) ^ 2 := by
  let conv := odlyzkoBumpComplex ⋆[ContinuousLinearMap.mul ℂ ℂ] odlyzkoBumpComplex
  have hfun : odlyzkoHComplex = fun x ↦ (1 / 3 : ℂ) * conv x := by
    funext x
    exact odlyzkoHComplex_eq_convolution x
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
  rw [Real.fourier_mul_convolution_eq odlyzkoBumpComplex_integrable
    odlyzkoBumpComplex_integrable]
  ring

/-- The Fourier transform of `H` has nonnegative real part at every real
frequency. -/
theorem odlyzkoH_fourier_re_nonneg (w : ℝ) :
    0 ≤ (𝓕 odlyzkoHComplex w).re := by
  rw [odlyzkoH_fourier_eq_square, odlyzkoBumpComplex_fourier_real]
  norm_num [pow_two]
  exact mul_self_nonneg _

/-- The Fourier transform of `H` is real at every real frequency. -/
theorem odlyzkoH_fourier_im_eq_zero (w : ℝ) :
    (𝓕 odlyzkoHComplex w).im = 0 := by
  rw [odlyzkoH_fourier_eq_square, odlyzkoBumpComplex_fourier_real]
  norm_num [pow_two]

/-- The scaled auxiliary function `x ↦ H(x / 4)`, viewed as complex-valued. -/
def odlyzkoH4Complex (x : ℝ) : ℂ := odlyzkoHComplex (x / 4)

/-- Exact Fourier scaling for the auxiliary function used in the `b = 4` kernel. -/
theorem odlyzkoH4_fourier_eq (w : ℝ) :
    𝓕 odlyzkoH4Complex w = 4 * 𝓕 odlyzkoHComplex (4 * w) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  calc
    (∫ x : ℝ, 𝐞 (-(x * w)) • odlyzkoH4Complex x) =
        ∫ x : ℝ, (fun y : ℝ ↦
          𝐞 (-(y * (4 * w))) • odlyzkoHComplex y) (x / 4) := by
      congr with x
      simp only [odlyzkoH4Complex]
      congr 2
      ring
    _ = |(4 : ℝ)| • ∫ y : ℝ,
        𝐞 (-(y * (4 * w))) • odlyzkoHComplex y :=
      Measure.integral_comp_div (fun y : ℝ ↦
        𝐞 (-(y * (4 * w))) • odlyzkoHComplex y) 4
    _ = 4 * ∫ y : ℝ, 𝐞 (-(y * (4 * w))) • odlyzkoHComplex y := by
      norm_num [smul_eq_mul]

/-- The Fourier transform of the scaled auxiliary function has nonnegative real part. -/
theorem odlyzkoH4_fourier_re_nonneg (w : ℝ) :
    0 ≤ (𝓕 odlyzkoH4Complex w).re := by
  rw [odlyzkoH4_fourier_eq]
  simpa using mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
    (odlyzkoH_fourier_re_nonneg (4 * w))

/-- The Fourier transform of the scaled auxiliary function is real. -/
theorem odlyzkoH4_fourier_im_eq_zero (w : ℝ) :
    (𝓕 odlyzkoH4Complex w).im = 0 := by
  rw [odlyzkoH4_fourier_eq]
  norm_num [odlyzkoH_fourier_im_eq_zero]

/-- The scaled auxiliary function is integrable. -/
theorem odlyzkoH4Complex_integrable : Integrable odlyzkoH4Complex volume := by
  exact odlyzkoHComplex_integrable.comp_div (by norm_num)

end
end TraceEuclidean
