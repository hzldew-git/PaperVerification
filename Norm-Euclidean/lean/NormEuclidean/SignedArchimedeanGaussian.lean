import NormEuclidean.SignedRealGaussian
import NormEuclidean.TraceGaussianFourier
import NormEuclidean.RayHeckeSigns

/-!
# Signed Gaussian Fourier transformation in the actual infinite adele ring

The real factors use the parity of the actual ray conductor. Complex
factors retain the trace-normalized Gaussian and twice planar measure.
Thus the product formula has no unspecified measure or Fourier constant.
-/

noncomputable section

namespace NormEuclidean.SignedArchimedeanGaussian

open NumberField NumberField.InfinitePlace MeasureTheory InfiniteTraceProduct InfiniteTraceFourier
open TraceGaussianFourier RayHeckeCharacter
open scoped NumberField Classical FourierTransform

variable (F : Type*) [Field F] [NumberField F]

def gaussian (a : RealPlace F → Fin 2) (t : ℝ) : InfiniteAdeleRing F → ℂ :=
  tensor F (fun v ↦ SignedRealGaussian.test (a v) (t : ℂ)) (fun _ ↦ complexGaussian t)

def scale (a : RealPlace F → Fin 2) (t : ℝ) : ℂ :=
  (∏ v, (-Complex.I / (t : ℂ)) ^ (a v).val * (1 / (t : ℂ) ^ (1 / 2 : ℂ))) *
    ((t : ℂ)⁻¹) ^ nrComplexPlaces F

/-- Fourier transformation uses the fixed global trace character and fixed Haar measure. -/
theorem fourier (a : RealPlace F → Fin 2) (t : ℝ) (ht : 0 < t)
    (w : InfiniteAdeleRing F) :
    InfiniteTraceFourier.fourier F (gaussian F a t) w =
      scale F a t * gaussian F a t⁻¹ w := by
  unfold gaussian
  rw [fourier_tensor]
  simp only [tensor, SignedRealGaussian.fourier_test _ (t : ℂ) (by simpa using ht),
    complex_fourier t ht, Complex.ofReal_inv, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, scale, nrComplexPlaces]
  ring

theorem even_eq (t : ℝ) : gaussian F (fun _ ↦ 0) t = TraceGaussianFourier.gaussian F t := by
  rfl

/-- Reflection records every real parity, rather than silently imposing evenness. -/
theorem reflection (a : RealPlace F → Fin 2) (t : ℝ) (w : InfiniteAdeleRing F) :
    gaussian F a t (-w) = (∏ v, (-1 : ℂ) ^ (a v).val) * gaussian F a t w := by
  unfold gaussian tensor
  simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply,
    SignedRealGaussian.test_neg, Finset.prod_mul_distrib, complexGaussian, norm_neg]
  ring

/-- Any odd real factor removes the zero vector term of the actual global test function. -/
theorem zero_of_odd (a : RealPlace F → Fin 2) (v : RealPlace F) (hv : a v = 1) (t : ℝ) :
    gaussian F a t 0 = 0 := by
  unfold gaussian tensor
  simp only [map_zero, Prod.fst_zero, Pi.zero_apply]
  have hz : (∏ w : RealPlace F, SignedRealGaussian.test (a w) (t : ℂ) 0) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv, SignedRealGaussian.test, SignedRealGaussian.odd_zero]
  rw [hz, zero_mul]

variable {F} {m : RayClass.Modulus F}

/-- The parity vector is constructed from the least full conductor of the actual character. -/
def parity (χ : Character m) (v : RealPlace F) : Fin 2 :=
  ⟨RayHeckeSigns.parity χ v, lt_of_le_of_lt (RayHeckeSigns.parity_le_one χ v) (by decide)⟩

theorem parity_sign (χ : Character m) (v : RealPlace F) :
    RayHeckeSigns.localCharacter χ v (-1) = (-1 : ℂ) ^ (parity χ v).val :=
  RayHeckeSigns.negative_eq_parity χ v

/-- The actual ray-character archimedean test, with no separate choice of signs. -/
def rayGaussian (χ : Character m) (t : ℝ) : InfiniteAdeleRing F → ℂ :=
  gaussian F (parity χ) t

theorem ray_fourier (χ : Character m) (t : ℝ) (ht : 0 < t) (w : InfiniteAdeleRing F) :
    InfiniteTraceFourier.fourier F (rayGaussian χ t) w =
      scale F (parity χ) t * rayGaussian χ t⁻¹ w := fourier F _ t ht w

end NormEuclidean.SignedArchimedeanGaussian
