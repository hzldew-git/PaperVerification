import NormEuclidean.SignedArchimedeanGaussian
import NormEuclidean.ArchimedeanIdealTheta

/-!
# Signed Gaussian kernels in the original mixed coordinates

The polynomial records each real parity. Both its trace-Gaussian
comparison and its translation by positive unit logs are proved here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.SignedGaussianShape

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem ArchimedeanLogScale
open InfiniteTraceProduct
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

def polynomial (a : RealPlace F → Fin 2) (x : mixedSpace F) : ℝ :=
  ∏ v, (x.1 v) ^ (a v).val

def kernel (a : RealPlace F → Fin 2) (t : ℝ) (r : InfinitePlace F → ℝ)
    (x : mixedSpace F) : ℝ :=
  polynomial F a (scale F r x) * Real.exp (-Real.pi * t *
    ‖IdealTheta.euclidean F (scale F r x)‖ ^ 2)

/-- The coordinate kernel is the already Fourier-transformed trace Gaussian. -/
theorem gaussian_factor (a : RealPlace F → Fin 2) (t : ℝ) (y : InfiniteAdeleRing F) :
    SignedArchimedeanGaussian.gaussian F a t y =
      (polynomial F a (InfiniteTraceHaar.coordinates F y) : ℂ) *
        TraceGaussianFourier.gaussian F t y := by
  have h (v : RealPlace F) (x : ℝ) :
      SignedRealGaussian.test (a v) (t : ℂ) x =
        (x : ℂ) ^ (a v).val * TraceGaussianFourier.realGaussian t x := by
    generalize a v = b
    fin_cases b <;> simp [SignedRealGaussian.test, SignedRealGaussian.even,
      SignedRealGaussian.odd, TraceGaussianFourier.realGaussian]
  simp only [SignedArchimedeanGaussian.gaussian, TraceGaussianFourier.gaussian,
    InfiniteTraceFourier.tensor, h, Finset.prod_mul_distrib, polynomial,
    Complex.ofReal_prod, Complex.ofReal_pow]
  ring

theorem kernel_trace (a : RealPlace F → Fin 2) (t : ℝ)
    (r : InfinitePlace F → ℝ) (x : mixedSpace F) :
    (kernel F a t r x : ℂ) = SignedArchimedeanGaussian.gaussian F a t
      ((InfiniteTraceHaar.coordinates F).symm (scale F r x)) := by
  rw [gaussian_factor, IdealThetaNormalization.gaussian_eq_exp]
  simp only [ContinuousAddEquiv.apply_symm_apply]
  rw [← IdealThetaNormalization.euclidean_norm_sq]
  simp only [kernel, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_pow]

theorem real_norm_le (x : mixedSpace F) (v : RealPlace F) :
    ‖x.1 v‖ ≤ ‖IdealTheta.euclidean F x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Real.norm_eq_abs, sq_abs, IdealThetaNormalization.euclidean_norm_sq]
  have h := Finset.single_le_sum (fun w (_ : w ∈ Finset.univ) ↦ sq_nonneg (x.1 w))
    (Finset.mem_univ v)
  have h' : 0 ≤ 2 * ∑ w : ComplexPlace F, ‖x.2 w‖ ^ 2 := by positivity
  exact h.trans (le_add_of_nonneg_right h')

theorem polynomial_bound (a : RealPlace F → Fin 2) (R : ℝ)
    (r : InfinitePlace F → ℝ) (hr : ‖r‖ ≤ R) (x : mixedSpace F) :
    ‖polynomial F a (scale F r x)‖ ≤
      Real.exp R ^ (∑ v, (a v).val) * ‖IdealTheta.euclidean F x‖ ^ (∑ v, (a v).val) := by
  rw [polynomial, norm_prod]
  calc
    _ ≤ ∏ v, (Real.exp R * ‖IdealTheta.euclidean F x‖) ^ (a v).val := by
      apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
      intro v _
      rw [norm_pow, scale_real, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply pow_le_pow_left₀ (by positivity)
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr ((le_abs_self (r v)).trans
          ((show |r v| ≤ ‖r‖ by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm r v.1).trans hr))
      · exact real_norm_le F x v
      · exact norm_nonneg _
      · exact (Real.exp_pos _).le
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, mul_pow]

theorem kernel_bound (a : RealPlace F → Fin 2) (t : ℝ) (ht : 0 < t)
    (R : ℝ) (r : InfinitePlace F → ℝ) (hr : ‖r‖ ≤ R) (x : F) :
    ‖kernel F a t r (mixedEmbedding F x)‖ ≤
      Real.exp R ^ (∑ v, (a v).val) *
        (‖IdealTheta.embedding F x‖ ^ (∑ v, (a v).val) *
          Real.exp (-Real.pi * (t * Real.exp (-R) ^ 2) * ‖IdealTheta.embedding F x‖ ^ 2)) := by
  rw [kernel, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := mul_le_mul (polynomial_bound F a R r hr (mixedEmbedding F x))
    (ArchimedeanIdealTheta.term_le F t ht R r hr x) (Real.exp_pos _).le (by positivity)
  simpa only [IdealTheta.embedding, mul_assoc] using h

theorem real_unit (l : logSpace F) (u : (𝓞 F)ˣ) (x : mixedSpace F) (v : RealPlace F)
    (hu : 0 < embedding_of_isReal v.2 (u : F)) :
    (scale F (UnitLogShape.parameter F (l + logEmbedding F (Additive.ofMul u))) x).1 v =
      (scale F (UnitLogShape.parameter F l) (u • x)).1 v := by
  rw [scale_real, scale_real, map_add, Pi.add_apply, UnitLogShape.parameter_logEmbedding,
    Real.exp_add, Real.exp_log (Units.pos_at_place u v), unitSMul_smul]
  change Real.exp _ * v.1 (u : F) * x.1 v =
    Real.exp _ * ((mixedEmbedding F (u : F)).1 v * x.1 v)
  rw [mixedEmbedding_apply_isReal, ← norm_embedding_of_isReal v.2,
    Real.norm_eq_abs, abs_of_pos hu]
  ring

theorem unit_translate (a : RealPlace F → Fin 2) (t : ℝ) (l : logSpace F)
    (u : (𝓞 F)ˣ) (hu : ∀ v, a v = 1 → 0 < embedding_of_isReal v.2 (u : F))
    (x : mixedSpace F) :
    kernel F a t (UnitLogShape.parameter F (l + logEmbedding F (Additive.ofMul u))) x =
      kernel F a t (UnitLogShape.parameter F l) (u • x) := by
  unfold kernel
  rw [UnitLogShape.unit_energy]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  by_cases ha : a v = 0
  · simp [ha]
  · have ha' : a v = 1 := by omega
    rw [ha']
    simp only [Fin.val_one, pow_one]
    exact real_unit F l u x v (hu v ha')

theorem continuous_kernel (a : RealPlace F → Fin 2) (t : ℝ) (x : F) :
    Continuous (fun r : InfinitePlace F → ℝ ↦ kernel F a t r (mixedEmbedding F x)) := by
  unfold kernel
  apply Continuous.mul _ (ArchimedeanIdealTheta.continuous_term F t x)
  unfold polynomial
  apply continuous_finsetProd
  intro v _
  simp only [scale_real]
  exact ((Real.continuous_exp.comp (continuous_apply v.1)).mul continuous_const).pow _

end NormEuclidean.SignedGaussianShape
