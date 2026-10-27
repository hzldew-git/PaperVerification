import NormEuclidean.IdealThetaNormalization
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# Actual independent archimedean logarithmic scaling

The original real and complex mixed coordinates are multiplied by the
positive factors exp(r_v). Complex-place multiplicities are retained
in the Gaussian energy and in the actual multiplicative mixed norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.ArchimedeanLogScale

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

/-- The actual diagonal archimedean scaling, with an actual continuous linear inverse. -/
def scale (r : InfinitePlace F → ℝ) : mixedSpace F ≃L[ℝ] mixedSpace F :=
  (ContinuousLinearEquiv.piCongrRight fun w : {w : InfinitePlace F // IsReal w} ↦
    (LinearEquiv.smulOfUnit (M := ℝ) (Units.mk0 (Real.exp (r w))
      (Real.exp_ne_zero _))).toContinuousLinearEquiv).prodCongr
    (ContinuousLinearEquiv.piCongrRight fun w : {w : InfinitePlace F // IsComplex w} ↦
      (LinearEquiv.smulOfUnit (M := ℂ) (Units.mk0 (Real.exp (r w))
        (Real.exp_ne_zero _))).toContinuousLinearEquiv)

omit [NumberField F] in
@[simp]
theorem scale_real (r : InfinitePlace F → ℝ) (x : mixedSpace F)
    (w : {w : InfinitePlace F // IsReal w}) : (scale F r x).1 w = Real.exp (r w) * x.1 w := rfl

omit [NumberField F] in
@[simp]
theorem scale_complex (r : InfinitePlace F → ℝ) (x : mixedSpace F)
    (w : {w : InfinitePlace F // IsComplex w}) :
    (scale F r x).2 w = Real.exp (r w) • x.2 w := rfl

omit [NumberField F] in
/-- Adding actual logarithmic parameters composes their original diagonal scalings. -/
theorem scale_add (r s : InfinitePlace F → ℝ) (x : mixedSpace F) :
    scale F (r + s) x = scale F r (scale F s x) := by
  apply Prod.ext
  · funext w
    simp only [scale_real, Pi.add_apply, Real.exp_add, mul_assoc]
  · funext w
    simp only [scale_complex, Pi.add_apply, Real.exp_add, mul_smul]

omit [NumberField F] in
@[simp]
theorem scale_zero (x : mixedSpace F) : scale F 0 x = x := by
  apply Prod.ext
  · funext w
    simp only [scale_real, Pi.zero_apply, Real.exp_zero, one_mul]
  · funext w
    simp only [scale_complex, Pi.zero_apply, Real.exp_zero, one_smul]

omit [NumberField F] in
/-- The actual inverse scaling uses exactly the negative logarithmic parameter. -/
theorem scale_neg (r : InfinitePlace F → ℝ) (x : mixedSpace F) :
    scale F (-r) (scale F r x) = x := by
  rw [← scale_add, neg_add_cancel, scale_zero]

/-- The Euclidean Gaussian energy retains each original real and complex coordinate. -/
theorem energy (r : InfinitePlace F → ℝ) (x : mixedSpace F) :
    ‖IdealTheta.euclidean F (scale F r x)‖ ^ 2 =
      (∑ w : {w : InfinitePlace F // IsReal w}, Real.exp (r w) ^ 2 * (x.1 w) ^ 2) +
        2 * ∑ w : {w : InfinitePlace F // IsComplex w},
          Real.exp (r w) ^ 2 * ‖x.2 w‖ ^ 2 := by
  rw [IdealThetaNormalization.euclidean_norm_sq]
  simp only [IdealThetaNormalization.energy, scale_real, scale_complex, mul_pow,
    _root_.norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

omit [NumberField F] in
/-- Joint scaling is continuous on the original mixed topology. -/
theorem continuous : Continuous (fun p : (InfinitePlace F → ℝ) × mixedSpace F ↦
    scale F p.1 p.2) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    change Continuous (fun p : (InfinitePlace F → ℝ) × mixedSpace F ↦
      Real.exp (p.1 w) * p.2.1 w)
    fun_prop
  · apply continuous_pi
    intro w
    change Continuous (fun p : (InfinitePlace F → ℝ) × mixedSpace F ↦
      Real.exp (p.1 w) • p.2.2 w)
    fun_prop

omit [NumberField F] in
/-- Each actual place norm is multiplied by the positive exponential at that place. -/
theorem normAtPlace_scale (r : InfinitePlace F → ℝ) (x : mixedSpace F)
    (w : InfinitePlace F) :
    normAtPlace w (scale F r x) = Real.exp (r w) * normAtPlace w x := by
  by_cases hw : IsReal w
  · simp only [normAtPlace_apply_of_isReal hw, scale_real, norm_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · simp only [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw),
      scale_complex, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The multiplicative norm records the actual archimedean multiplicities. -/
theorem multiplicative_norm_scale (r : InfinitePlace F → ℝ) (x : mixedSpace F) :
    mixedEmbedding.norm (scale F r x) =
      Real.exp (∑ w, (mult w : ℝ) * r w) * mixedEmbedding.norm x := by
  simp only [mixedEmbedding.norm_apply, normAtPlace_scale, mul_pow, Finset.prod_mul_distrib,
    ← Real.exp_nat_mul, ← Real.exp_sum]

/-- Equality of actual place norms implies equality of the trace-normalized Gaussian energy. -/
theorem energy_eq_of_place_norm (x y : mixedSpace F)
    (h : ∀ w, normAtPlace w x = normAtPlace w y) :
    ‖IdealTheta.euclidean F x‖ ^ 2 = ‖IdealTheta.euclidean F y‖ ^ 2 := by
  rw [IdealThetaNormalization.euclidean_norm_sq, IdealThetaNormalization.euclidean_norm_sq]
  unfold IdealThetaNormalization.energy
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    have he := congrArg (fun t : ℝ ↦ t ^ 2) (h w)
    simpa only [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs, sq_abs] using he
  · congr 1
    apply Finset.sum_congr rfl
    intro w _
    exact congrArg (fun t : ℝ ↦ t ^ 2)
      (by simpa only [normAtPlace_apply_of_isComplex w.2] using h w)

end NormEuclidean.ArchimedeanLogScale
