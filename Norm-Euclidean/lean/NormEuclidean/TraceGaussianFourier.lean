import NormEuclidean.InfiniteTraceFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Fourier transforms for the actual infinite trace measure

The real Gaussian has exponent `-pi*t*x^2`; the complex Gaussian has
exponent `-2*pi*t*|z|^2`. Fourier transformation uses the previously
constructed negative trace character and twice planar measure at every
complex place. The resulting constants are calculated from those measures.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.TraceGaussianFourier

open NumberField NumberField.InfinitePlace MeasureTheory ComplexConjugate InfiniteTraceProduct
open ArchimedeanTraceFourier InfiniteTraceFourier
open scoped FourierTransform RealInnerProductSpace NumberField Classical

/-- The standard Gaussian on a real completion. -/
def realGaussian (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (t : ℂ) * (x : ℂ) ^ 2)

/-- The factor two matches the actual complex trace pairing. -/
def complexGaussian (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-2 * Real.pi * (t : ℂ) * (‖z‖ : ℂ) ^ 2)

/-- The real local Fourier transform has the standard reciprocal square-root factor. -/
theorem real_fourier (t : ℝ) (ht : 0 < t) (w : ℝ) :
    𝓕 (realGaussian t) w =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * realGaussian t⁻¹ w := by
  unfold realGaussian
  rw [fourier_gaussian_pi (by simpa : 0 < (t : ℂ).re)]
  simp only [Complex.ofReal_inv, div_eq_mul_inv]

/-- The actual complex trace transform gives one reciprocal parameter, with no extra two. -/
theorem complex_fourier (t : ℝ) (ht : 0 < t) (w : ℂ) :
    complexFourier (complexGaussian t) w = (t : ℂ)⁻¹ * complexGaussian t⁻¹ w := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hb : 0 < ((2 : ℂ) * Real.pi * t).re := by
    simpa using mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) ht
  rw [complex_eq]
  have hfun : complexGaussian t =
      (fun z : ℂ ↦ Complex.exp (-((2 : ℂ) * Real.pi * t) * (‖z‖ : ℂ) ^ 2)) := by
    funext z
    unfold complexGaussian
    congr 1
    ring
  rw [hfun, fourier_gaussian_innerProductSpace hb]
  have hn : ‖(2 : ℝ) • conj w‖ = 2 * ‖w‖ := by
    simp
  rw [hn, Complex.finrank_real_complex]
  have hp : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
  rw [hp, Complex.cpow_one]
  unfold complexGaussian
  push_cast
  have hc : (2 : ℂ) * ((Real.pi : ℂ) / (2 * Real.pi * t)) = (t : ℂ)⁻¹ := by
    field_simp
  have he : -(Real.pi : ℂ) ^ 2 * (2 * (‖w‖ : ℂ)) ^ 2 / (2 * Real.pi * t) =
      -2 * Real.pi * (t : ℂ)⁻¹ * (‖w‖ : ℂ) ^ 2 := by
    field_simp
  rw [← mul_assoc, hc, he]

variable (F : Type*) [Field F] [NumberField F]

/-- The actual separated Gaussian on the unchanged infinite adele ring. -/
def gaussian (t : ℝ) : InfiniteAdeleRing F → ℂ :=
  tensor F (fun _ ↦ realGaussian t) (fun _ ↦ complexGaussian t)

/-- The exact archimedean Fourier scale, recorded separately at real and complex places. -/
def scale (t : ℝ) : ℂ :=
  (1 / (t : ℂ) ^ (1 / 2 : ℂ)) ^ nrRealPlaces F * ((t : ℂ)⁻¹) ^ nrComplexPlaces F

/-- Fourier transformation of the actual global Gaussian with its fixed trace normalization. -/
theorem fourier_gaussian (t : ℝ) (ht : 0 < t) (w : InfiniteAdeleRing F) :
    fourier F (gaussian F t) w = scale F t * gaussian F t⁻¹ w := by
  unfold gaussian
  rw [fourier_tensor]
  simp only [tensor, real_fourier t ht, complex_fourier t ht,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    scale, nrRealPlaces, nrComplexPlaces]
  ring

/-- The real and complex local constants combine into the actual field degree. -/
theorem scale_eq_degree (t : ℝ) (ht : 0 < t) :
    scale F t = (t : ℂ) ^ (-((Module.finrank ℚ F : ℂ) / 2)) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  calc
    scale F t = ((t : ℂ) ^ (-(1 / 2 : ℂ))) ^ nrRealPlaces F *
        ((t : ℂ) ^ (-1 : ℂ)) ^ nrComplexPlaces F := by
      simp only [scale, one_div, Complex.cpow_neg, Complex.cpow_one]
    _ = (t : ℂ) ^ ((nrRealPlaces F : ℂ) * (-(1 / 2 : ℂ))) *
        (t : ℂ) ^ ((nrComplexPlaces F : ℂ) * (-1 : ℂ)) := by
      rw [Complex.cpow_nat_mul, Complex.cpow_nat_mul]
    _ = (t : ℂ) ^ ((nrRealPlaces F : ℂ) * (-(1 / 2 : ℂ)) +
        (nrComplexPlaces F : ℂ) * (-1 : ℂ)) := (Complex.cpow_add _ _ ht0).symm
    _ = _ := by
      congr 1
      have hdim : (Module.finrank ℚ F : ℂ) =
          (nrRealPlaces F : ℂ) + 2 * (nrComplexPlaces F : ℂ) := by
        exact_mod_cast (card_add_two_mul_card_eq_rank F).symm
      rw [hdim]
      ring

/-- The actual archimedean Gaussian transform has the usual degree-over-two scale. -/
theorem fourier_gaussian_degree (t : ℝ) (ht : 0 < t) (w : InfiniteAdeleRing F) :
    fourier F (gaussian F t) w =
      (t : ℂ) ^ (-((Module.finrank ℚ F : ℂ) / 2)) * gaussian F t⁻¹ w := by
  rw [fourier_gaussian F t ht w, scale_eq_degree F t ht]

/-- The zero argument gives one in the original, trace-normalized Gaussian. -/
theorem gaussian_zero (t : ℝ) : gaussian F t 0 = 1 := by
  unfold gaussian tensor
  rw [map_zero (InfiniteTraceHaar.coordinates F)]
  simp [realGaussian, complexGaussian]

/-- Integrating the actual Gaussian yields the computed archimedean scale. -/
theorem integral_gaussian (t : ℝ) (ht : 0 < t) :
    (∫ a : InfiniteAdeleRing F, gaussian F t a ∂InfiniteTraceHaar.haar F) =
      (t : ℂ) ^ (-((Module.finrank ℚ F : ℂ) / 2)) := by
  have h := fourier_gaussian_degree F t ht 0
  simpa only [fourier, mul_zero, AddChar.map_zero_eq_one, one_mul, gaussian_zero, mul_one] using h

end NormEuclidean.TraceGaussianFourier
