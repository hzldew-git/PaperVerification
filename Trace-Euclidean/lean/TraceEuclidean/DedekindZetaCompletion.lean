import TraceEuclidean.DedekindZetaUnorderedZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The gamma normalization of the conditional Dedekind-zeta completion

This file checks the archimedean normalization and zero locations in the
open critical strip. It does not construct the entire continuation or prove
the functional equation. Both remain analytic tasks.
-/

namespace TraceEuclidean

noncomputable section

open Filter
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- HSW's archimedean factor, written with Deligne's real Gamma function.
The two factors at each complex place are `Gammaℝ s` and `Gammaℝ (s+1)`. -/
def hSWGammaFactor (s : ℂ) : ℂ :=
  (Complex.Gammaℝ s) ^
      (NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K) *
    (Complex.Gammaℝ (s + 1)) ^ NumberField.InfinitePlace.nrComplexPlaces K

/-- The same factor in the conventional real-place/complex-place notation. -/
def completedArchimedeanFactor (s : ℂ) : ℂ :=
  (Complex.Gammaℝ s) ^ NumberField.InfinitePlace.nrRealPlaces K *
    (Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K

/-- The HSW Gamma normalization agrees exactly with mathlib's Deligne factors. -/
theorem hswGammaFactor_eq_archimedeanFactor (s : ℂ) :
    hSWGammaFactor K s = completedArchimedeanFactor K s := by
  unfold hSWGammaFactor completedArchimedeanFactor
  rw [pow_add]
  calc
    _ = (Complex.Gammaℝ s) ^ NumberField.InfinitePlace.nrRealPlaces K *
        ((Complex.Gammaℝ s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (Complex.Gammaℝ (s + 1)) ^ NumberField.InfinitePlace.nrComplexPlaces K) := by
          ring
    _ = _ := by rw [← mul_pow, Complex.Gammaℝ_mul_Gammaℝ_add_one]

/-- Every archimedean factor is nonzero in the open critical strip. -/
theorem completedArchimedeanFactor_ne_zero {s : ℂ} (hs : 0 < s.re) :
    completedArchimedeanFactor K s ≠ 0 := by
  have hGamma : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hShift : Complex.Gammaℝ (s + 1) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hComplex : Complex.Gammaℂ s ≠ 0 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero hGamma hShift
  unfold completedArchimedeanFactor
  exact mul_ne_zero (pow_ne_zero _ hGamma) (pow_ne_zero _ hComplex)

/-- The factor multiplying the pole-removed Dedekind zeta function. -/
def completedMultiplier (s : ℂ) : ℂ :=
  s * (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)) *
    completedArchimedeanFactor K s

theorem completedMultiplier_ne_zero {s : ℂ} (hs : 0 < s.re) :
    completedMultiplier K s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hd : ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    linarith [abs_discr_ge_one K]
  have hPow : (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hd]
    exact Complex.exp_ne_zero _
  unfold completedMultiplier
  exact mul_ne_zero (mul_ne_zero hs0 hPow)
    (completedArchimedeanFactor_ne_zero K hs)

/-- The source-normalized completed function, conditional on the entire
pole-removed continuation `Z`. Its global analyticity and functional
equation are not proved by this definition. -/
def completedFromRegularization (Z : DedekindZetaRegularization K)
    (s : ℂ) : ℂ :=
  completedMultiplier K s * Z.value s

/-- The completed function and the existing regularization have precisely
the same zero *positions* in the open critical strip. -/
theorem completed_zero_iff_regularized_zero
    (Z : DedekindZetaRegularization K) {s : ℂ} (hs : 0 < s.re) :
    completedFromRegularization K Z s = 0 ↔ Z.value s = 0 := by
  unfold completedFromRegularization
  simp only [mul_eq_zero, completedMultiplier_ne_zero K hs, false_or]

private theorem gammaR_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hne := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hInv : DifferentiableAt ℂ (fun z : ℂ ↦ (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hDouble := hInv.inv (inv_ne_zero hne)
  change DifferentiableAt ℂ (fun z : ℂ ↦ ((Complex.Gammaℝ z)⁻¹)⁻¹) s at hDouble
  simpa only [inv_inv] using hDouble

/-- The multiplier is analytic locally wherever the real part is positive.
This is enough to compare analytic zero orders in the critical strip. -/
theorem completedMultiplier_analyticAt {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (completedMultiplier K) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hOpen : {z : ℂ | 0 < z.re} ∈ 𝓝 s :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
  filter_upwards [hOpen] with z hz
  have hG : DifferentiableAt ℂ Complex.Gammaℝ z :=
    gammaR_differentiableAt_of_re_pos hz
  have hShiftPos : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hShift : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gammaℝ (w + 1)) z :=
    (gammaR_differentiableAt_of_re_pos hShiftPos).comp z
      (differentiableAt_id.add_const 1)
  have hGC : DifferentiableAt ℂ Complex.Gammaℂ z := by
    have heq : Complex.Gammaℂ =
        (fun w : ℂ ↦ Complex.Gammaℝ w * Complex.Gammaℝ (w + 1)) := by
      funext w
      exact (Complex.Gammaℝ_mul_Gammaℝ_add_one w).symm
    rw [heq]
    exact hG.mul hShift
  have hd : ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    linarith [abs_discr_ge_one K]
  have hPow : Differentiable ℂ
      (fun w : ℂ ↦ (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (w / 2))) := by
    have heq : (fun w : ℂ ↦ (((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (w / 2))) =
        (fun w : ℂ ↦ Complex.exp
          (Complex.log ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) * (w / 2))) := by
      funext w
      exact Complex.cpow_def_of_ne_zero hd _
    rw [heq]
    fun_prop
  unfold completedMultiplier completedArchimedeanFactor
  exact ((differentiableAt_id.mul hPow.differentiableAt).mul
    ((hG.pow _).mul (hGC.pow _)))

/-- The nonzero Gamma and discriminant factor preserves every zero's
analytic multiplicity in the open critical strip. -/
theorem completed_zero_order_eq_regularized_zero_order
    (Z : DedekindZetaRegularization K) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (completedFromRegularization K Z) s =
      analyticOrderNatAt Z.value s := by
  have hMul : AnalyticAt ℂ (completedMultiplier K) s :=
    completedMultiplier_analyticAt K hs
  have hZero : analyticOrderAt (completedMultiplier K) s = 0 :=
    (hMul.analyticOrderAt_eq_zero).2 (completedMultiplier_ne_zero K hs)
  unfold completedFromRegularization
  change analyticOrderNatAt ((completedMultiplier K) * Z.value) s =
    analyticOrderNatAt Z.value s
  simp only [analyticOrderNatAt,
    analyticOrderAt_mul hMul (Z.analytic s (Set.mem_univ s)), hZero, zero_add]

end
end TraceEuclidean
