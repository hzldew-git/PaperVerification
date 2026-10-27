import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Real Gaussian test functions with both Hecke parities

The Fourier convention here is exp(-2 pi i x y), with ordinary Lebesgue
measure. The odd test function is x times the Gaussian. Its extra factor
-i/b is retained explicitly; replacing it by the even Gaussian would
annihilate an odd character.
-/

noncomputable section

namespace NormEuclidean.SignedRealGaussian

open Complex Real MeasureTheory FourierTransform
open scoped FourierTransform

def even (b : ℂ) (x : ℝ) : ℂ := Complex.exp (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2)

def odd (b : ℂ) (x : ℝ) : ℂ := (x : ℂ) * even b x

theorem even_neg (b : ℂ) (x : ℝ) : even b (-x) = even b x := by
  simp [even]

theorem odd_neg (b : ℂ) (x : ℝ) : odd b (-x) = -odd b x := by
  simp [odd, even_neg]

theorem even_zero (b : ℂ) : even b 0 = 1 := by simp [even]

theorem odd_zero (b : ℂ) : odd b 0 = 0 := by simp [odd]

theorem even_integrable (b : ℂ) (hb : 0 < b.re) : Integrable (even b) := by
  unfold even
  simpa only [neg_mul] using
    integrable_cexp_neg_mul_sq (show 0 < ((Real.pi : ℂ) * b).re by
      simpa using mul_pos Real.pi_pos hb)

theorem odd_integrable (b : ℂ) (hb : 0 < b.re) : Integrable (odd b) := by
  unfold odd even
  simpa only [neg_mul] using
    integrable_mul_cexp_neg_mul_sq (show 0 < ((Real.pi : ℂ) * b).re by
      simpa using mul_pos Real.pi_pos hb)

theorem even_derivative (b : ℂ) (x : ℝ) :
    HasDerivAt (even b) ((-2 * Real.pi * b) * odd b x) x := by
  unfold odd even
  have h := (((hasDerivAt_id (x : ℂ)).pow 2).const_mul (-(Real.pi : ℂ) * b)).cexp
  convert h.comp_ofReal using 1 <;> norm_num
  ring

theorem deriv_even (b : ℂ) : deriv (even b) = fun x ↦ (-2 * Real.pi * b) * odd b x :=
  funext fun x ↦ (even_derivative b x).deriv

theorem fourier_even (b : ℂ) (hb : 0 < b.re) :
    𝓕 (even b) = fun y : ℝ ↦ (1 / b ^ (1 / 2 : ℂ)) * even b⁻¹ y := by
  change 𝓕 (fun x : ℝ ↦ Complex.exp (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2)) = _
  rw [fourier_gaussian_pi hb]
  funext y
  unfold even
  congr 2

theorem fourier_const (c : ℂ) (f : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x ↦ c * f x) y = c * 𝓕 f y := by
  simp only [fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The odd Fourier transform has the essential imaginary and inverse-scale factor. -/
theorem fourier_odd (b : ℂ) (hb : 0 < b.re) (y : ℝ) :
    𝓕 (odd b) y = (-Complex.I / b) * (1 / b ^ (1 / 2 : ℂ)) * odd b⁻¹ y := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hd : Integrable (deriv (even b)) := by
    rw [deriv_even]
    exact (odd_integrable b hb).const_mul _
  have h := congrFun (fourier_deriv (even_integrable b hb)
    (fun x ↦ (even_derivative b x).differentiableAt) hd) y
  rw [deriv_even, fourier_const, fourier_even b hb] at h
  simp only [smul_eq_mul] at h
  apply mul_left_cancel₀ (show (-2 * (Real.pi : ℂ) * b) ≠ 0 by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) hb0)
  rw [h]
  simp only [odd]
  field_simp

/-- The finite parity records the two actual real characters. -/
def test (a : Fin 2) (b : ℂ) : ℝ → ℂ := if a = 0 then even b else odd b

theorem test_neg (a : Fin 2) (b : ℂ) (x : ℝ) :
    test a b (-x) = (-1 : ℂ) ^ a.val * test a b x := by
  fin_cases a <;> simp [test, even_neg, odd_neg]

theorem test_integrable (a : Fin 2) (b : ℂ) (hb : 0 < b.re) :
    Integrable (test a b) := by
  fin_cases a <;> simp only [test, Fin.isValue]
  · exact even_integrable b hb
  · exact odd_integrable b hb

theorem fourier_test (a : Fin 2) (b : ℂ) (hb : 0 < b.re) (y : ℝ) :
    𝓕 (test a b) y = (-Complex.I / b) ^ a.val *
      (1 / b ^ (1 / 2 : ℂ)) * test a b⁻¹ y := by
  fin_cases a
  · simpa [test] using congrFun (fourier_even b hb) y
  · simpa [test] using fourier_odd b hb y

end NormEuclidean.SignedRealGaussian
