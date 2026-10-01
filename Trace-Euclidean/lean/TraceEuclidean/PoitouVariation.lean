import TraceEuclidean.PoitouFullKernel
import TraceEuclidean.PoitouDifferentiability
import TraceEuclidean.BoundedVariationCriterion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace TraceEuclidean.PoitouKernel

noncomputable section

open MeasureTheory Set

def poitouScaledTestDeriv (y x : ℝ) : ℝ :=
  Real.sqrt y * poitouTestDeriv (Real.sqrt y * x)

theorem poitouScaledTest_hasDerivAt (y x : ℝ) :
    HasDerivAt (poitouScaledTest y) (poitouScaledTestDeriv y x) x := by
  have harg : HasDerivAt (fun z : ℝ ↦ Real.sqrt y * z) (Real.sqrt y) x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.sqrt y)
  unfold poitouScaledTest poitouScaledTestDeriv
  convert (poitouTest_hasDerivAt (Real.sqrt y * x)).comp x harg using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try simp only [Function.comp_def]
  all_goals ring

theorem poitouScaledTest_differentiable (y : ℝ) :
    Differentiable ℝ (poitouScaledTest y) :=
  fun x ↦ (poitouScaledTest_hasDerivAt y x).differentiableAt

theorem poitouScaledTestDeriv_abs_le {y : ℝ} (_hy : 0 ≤ y) (x : ℝ) :
    |poitouScaledTestDeriv y x| ≤ 9 / 2 * Real.sqrt y := by
  rw [poitouScaledTestDeriv, abs_mul, abs_of_nonneg (Real.sqrt_nonneg y)]
  have h := poitouTestDeriv_abs_le_nine_halves (Real.sqrt y * x)
  nlinarith [Real.sqrt_nonneg y]

theorem poitouTest_le_nine_fourths (x : ℝ) :
    poitouTest x ≤ 9 / 4 := by
  rw [poitouTest, ← sq_abs]
  have h := poitouAmplitude_abs_le_three_halves x
  have hs := pow_le_pow_left₀ (abs_nonneg (poitouAmplitude x)) h 2
  norm_num at hs ⊢
  exact hs

theorem poitouScaledTest_le_nine_fourths (y x : ℝ) :
    poitouScaledTest y x ≤ 9 / 4 :=
  poitouTest_le_nine_fourths _

def poitouSechDeriv (x : ℝ) : ℝ :=
  -(Real.sinh (x / 2) * (1 / 2 : ℝ)) / Real.cosh (x / 2) ^ 2

theorem poitouSech_hasDerivAt (x : ℝ) :
    HasDerivAt TraceEuclidean.odlyzkoSech (poitouSechDeriv x) x := by
  have harg : HasDerivAt (fun z : ℝ ↦ z / 2) (1 / 2 : ℝ) x := by
    simpa only [id_eq, one_div] using (hasDerivAt_id x).div_const 2
  have hc : HasDerivAt (fun z : ℝ ↦ Real.cosh (z / 2))
      (Real.sinh (x / 2) * (1 / 2 : ℝ)) x :=
    by
      convert (Real.hasDerivAt_cosh (x / 2)).comp x harg using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [Function.comp_def]
  have hi := hc.inv (Real.cosh_pos (x / 2)).ne'
  have heq : TraceEuclidean.odlyzkoSech =ᶠ[nhds x]
      (fun z : ℝ ↦ Real.cosh (z / 2))⁻¹ :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold TraceEuclidean.odlyzkoSech
      simp only [Pi.inv_apply, one_div]
  have hi' := hi.congr_of_eventuallyEq heq
  simpa only [poitouSechDeriv] using hi'

theorem poitouSech_differentiable :
    Differentiable ℝ TraceEuclidean.odlyzkoSech :=
  fun x ↦ (poitouSech_hasDerivAt x).differentiableAt

theorem poitouSechDeriv_abs_le (x : ℝ) :
    |poitouSechDeriv x| ≤
      (1 / 2 : ℝ) * TraceEuclidean.odlyzkoSech x := by
  unfold poitouSechDeriv
  have heq :
      -(Real.sinh (x / 2) * (1 / 2 : ℝ)) / Real.cosh (x / 2) ^ 2 =
        -(1 / 2 : ℝ) * Real.tanh (x / 2) *
          TraceEuclidean.odlyzkoSech x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    unfold TraceEuclidean.odlyzkoSech
    field_simp [(Real.cosh_pos (x / 2)).ne']
  rw [heq, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have htanh : |Real.tanh (x / 2)| ≤ 1 := (Real.abs_tanh_lt_one _).le
  have hsech : 0 ≤ TraceEuclidean.odlyzkoSech x := by
    unfold TraceEuclidean.odlyzkoSech
    positivity
  rw [abs_of_nonneg hsech]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by norm_num) htanh) hsech

def poitouFullKernelDeriv (y x : ℝ) : ℝ :=
  poitouScaledTestDeriv y x * TraceEuclidean.odlyzkoSech x +
    poitouScaledTest y x * poitouSechDeriv x

theorem poitouFullKernel_hasDerivAt (y x : ℝ) :
    HasDerivAt (poitouFullKernel y) (poitouFullKernelDeriv y x) x := by
  have h := (poitouScaledTest_hasDerivAt y x).mul (poitouSech_hasDerivAt x)
  have heq : poitouFullKernel y =ᶠ[nhds x]
      (poitouScaledTest y * TraceEuclidean.odlyzkoSech) :=
    Filter.Eventually.of_forall fun z ↦ by
      unfold poitouFullKernel TraceEuclidean.odlyzkoSech
      simp only [Pi.mul_apply]
      ring
  have h' := h.congr_of_eventuallyEq heq
  simpa only [poitouFullKernelDeriv] using h'

theorem poitouFullKernel_differentiable (y : ℝ) :
    Differentiable ℝ (poitouFullKernel y) :=
  fun x ↦ (poitouFullKernel_hasDerivAt y x).differentiableAt

theorem poitouFullKernelDeriv_abs_le {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    |poitouFullKernelDeriv y x| ≤
      (9 / 2 * Real.sqrt y + 9 / 8) *
        TraceEuclidean.odlyzkoSech x := by
  have hsd := poitouScaledTestDeriv_abs_le hy x
  have hst0 := poitouScaledTest_nonneg y x
  have hst := poitouScaledTest_le_nine_fourths y x
  have hsech0 : 0 ≤ TraceEuclidean.odlyzkoSech x := by
    unfold TraceEuclidean.odlyzkoSech
    positivity
  have hsechd := poitouSechDeriv_abs_le x
  unfold poitouFullKernelDeriv
  calc
    |poitouScaledTestDeriv y x * TraceEuclidean.odlyzkoSech x +
        poitouScaledTest y x * poitouSechDeriv x| ≤
        |poitouScaledTestDeriv y x| *
            |TraceEuclidean.odlyzkoSech x| +
          |poitouScaledTest y x| * |poitouSechDeriv x| := by
      simpa only [abs_mul] using
        (abs_add_le
          (poitouScaledTestDeriv y x * TraceEuclidean.odlyzkoSech x)
          (poitouScaledTest y x * poitouSechDeriv x))
    _ ≤ (9 / 2 * Real.sqrt y) * TraceEuclidean.odlyzkoSech x +
          (9 / 4) * ((1 / 2) * TraceEuclidean.odlyzkoSech x) := by
      rw [abs_of_nonneg hsech0, abs_of_nonneg hst0]
      gcongr
    _ = (9 / 2 * Real.sqrt y + 9 / 8) *
          TraceEuclidean.odlyzkoSech x := by ring

theorem poitouFullKernel_boundedVariation {y : ℝ} (hy : 0 ≤ y) :
    BoundedVariationOn (poitouFullKernel y) Set.univ := by
  let C : ℝ := 9 / 2 * Real.sqrt y + 9 / 8
  let B : ℝ → ℝ := fun x ↦ C * TraceEuclidean.odlyzkoSech x
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  apply boundedVariationOn_univ_of_integrable_deriv_bound
    (f := poitouFullKernel y) (B := B)
  · exact poitouFullKernel_continuous y
  · exact poitouFullKernel_differentiable y
  · intro x
    dsimp only [B]
    exact mul_nonneg hC (by
      unfold TraceEuclidean.odlyzkoSech
      positivity)
  · intro x
    rw [(poitouFullKernel_hasDerivAt y x).deriv, Real.norm_eq_abs]
    exact poitouFullKernelDeriv_abs_le hy x
  · exact TraceEuclidean.odlyzkoSech_integrable.const_mul C

end

end TraceEuclidean.PoitouKernel
