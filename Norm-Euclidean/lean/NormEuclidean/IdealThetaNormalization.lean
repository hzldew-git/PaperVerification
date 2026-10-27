import NormEuclidean.IdealTheta
import NormEuclidean.TraceGaussianFourier
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Comparing the literal ideal theta series and the fixed trace normalization

The square-root-of-two Euclidean weighting is identified with the
actual real and complex trace Gaussian. The fractional-ideal covolume
is computed in the already constructed trace Haar measure. These are
normalization comparisons, not a Poisson summation formula for ideals.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.IdealThetaNormalization

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory MeasureTheory.Measure IdealTheta TraceGaussianFourier
open InfiniteTraceFourier InfiniteTraceProduct
open scoped NumberField Classical nonZeroDivisors ENNReal

variable (F : Type*) [Field F] [NumberField F]

/-- The actual sum of archimedean squares with the complex trace multiplicities. -/
def energy (x : mixedSpace F) : ℝ :=
  (∑ w : RealPlace F, (x.1 w) ^ 2) + 2 * ∑ w : ComplexPlace F, ‖x.2 w‖ ^ 2

/-- The weighted Euclidean norm gives exactly the trace Gaussian energy. -/
theorem euclidean_norm_sq (x : mixedSpace F) : ‖euclidean F x‖ ^ 2 = energy F x := by
  change ‖WithLp.toLp 2
    (WithLp.toLp 2 x.1, WithLp.toLp 2 (Real.sqrt 2 • x.2))‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, PiLp.toLp_apply, Pi.smul_apply,
    _root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), energy, Finset.mul_sum]

/-- The actual original field elements inherit the same energy identity. -/
theorem embedding_norm_sq (x : F) :
    ‖embedding F x‖ ^ 2 = energy F (mixedEmbedding F x) :=
  euclidean_norm_sq F (mixedEmbedding F x)

/-- The existing separated Gaussian is the single Gaussian with this actual energy. -/
theorem gaussian_eq_exp (t : ℝ) (a : InfiniteAdeleRing F) :
    gaussian F t a = Complex.exp (-Real.pi * (t : ℂ) *
      (energy F (InfiniteTraceHaar.coordinates F a) : ℂ)) := by
  unfold gaussian tensor realGaussian complexGaussian
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  simp only [energy, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    ring

/-- The diagonal evaluation agrees with the Gaussian used by the original ideal theta sum. -/
theorem gaussian_diagonal (t : ℝ) (x : F) :
    gaussian F t (algebraMap F (InfiniteAdeleRing F) x) =
      Complex.exp (-Real.pi * (t : ℂ) * (‖embedding F x‖ : ℂ) ^ 2) := by
  rw [gaussian_eq_exp, InfiniteTraceHaar.coordinates_diagonal, ← embedding_norm_sq]
  rw [Complex.ofReal_pow]

/-- The literal ideal theta series is the actual trace Gaussian summed on diagonal ideal points. -/
theorem complexTheta_eq_diagonal (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) :
    complexTheta F I (t : ℂ) =
      ∑' x : {x : F // x ∈ (I : Set F)},
        gaussian F t (algebraMap F (InfiniteAdeleRing F) x.1) := by
  unfold complexTheta
  apply tsum_congr
  intro x
  exact (gaussian_diagonal F t x).symm

/-- The trace measure gives the actual ideal covolume, including nonprincipal ideals. -/
theorem ideal_covolume (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    InfiniteTraceHaar.mixedMeasure F (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis F I)) =
      ENNReal.ofReal ((FractionalIdeal.absNorm I.1 : ℝ) * Real.sqrt |(discr F : ℝ)|) := by
  rw [InfiniteTraceHaar.mixedMeasure, Measure.smul_apply, smul_eq_mul,
    volume_fundamentalDomain_fractionalIdealLatticeBasis]
  have h := InfiniteTraceHaar.mixed_integral_volume F
  rw [InfiniteTraceHaar.mixedMeasure, Measure.smul_apply, smul_eq_mul] at h
  rw [mul_left_comm, h]
  rw [ENNReal.ofReal_mul (by exact_mod_cast FractionalIdeal.absNorm_nonneg I.1)]

end NormEuclidean.IdealThetaNormalization
