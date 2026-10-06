import TraceEuclidean.PoitouGaussianRegularization

/-!
# Removing Poitou's Gaussian regularization

Poitou inserts a Gaussian factor and then lets its parameter tend to zero.
This file makes that limiting step explicit.  In the open critical strip the
unregularized tilted kernel is integrable, so dominated convergence applies
directly.
-/

namespace TraceEuclidean.PoitouKernel

noncomputable section

open Filter MeasureTheory Complex Set
open scoped Topology

/-- A concrete positive sequence of Gaussian parameters tending to zero. -/
def poitouGaussianEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem poitouGaussianEpsilon_pos (n : ℕ) : 0 < poitouGaussianEpsilon n := by
  exact one_div_pos.mpr (by positivity)

theorem poitouGaussianEpsilon_tendsto_zero :
    Tendsto poitouGaussianEpsilon atTop (𝓝 0) := by
  unfold poitouGaussianEpsilon
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem poitouGaussian_epsilon_tendsto_one (x : ℝ) :
    Tendsto (fun n : ℕ ↦ poitouGaussian (poitouGaussianEpsilon n) x)
      atTop (𝓝 1) := by
  have harg : Tendsto
      (fun n : ℕ ↦ -poitouGaussianEpsilon n * x ^ 2) atTop (𝓝 0) := by
    simpa using poitouGaussianEpsilon_tendsto_zero.neg.mul_const (x ^ 2)
  have h := Real.continuous_exp.continuousAt.tendsto.comp harg
  convert h using 1 <;> simp [poitouGaussian, Function.comp_def, neg_mul]

private theorem poitouPhi_integrand_norm_eq_tilted_norm
    (y : ℝ) (s : ℂ) (x : ℝ) :
    ‖(poitouFullKernel y x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))‖ =
      ‖poitouTiltedFullKernel y (s.re - 1 / 2) x‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp only [poitouTiltedFullKernel, norm_mul, norm_real, Real.norm_eq_abs]
  have hfull : 0 ≤ poitouFullKernel y x := poitouFullKernel_nonneg y x
  rw [abs_of_nonneg hfull, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (((s - (1 / 2 : ℂ)) * (x : ℂ)).re) =
      Real.exp ((s.re - 1 / 2) * x) := by
    congr 1
    simp [Complex.mul_re, Complex.sub_re]
  rw [hexp]
  ring

private theorem poitouGaussianRegularizedPhi_integrand_norm_le
    {y : ℝ} {s : ℂ} (n : ℕ) (x : ℝ) :
    ‖(poitouGaussianRegularizedKernel y (poitouGaussianEpsilon n) x : ℂ) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))‖ ≤
      ‖poitouTiltedFullKernel y (s.re - 1 / 2) x‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp only [poitouGaussianRegularizedKernel, norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (poitouFullKernel_nonneg y x)
    (poitouGaussian_nonneg _ x))]
  rw [show ‖poitouTiltedFullKernel y (s.re - 1 / 2) x‖ =
      poitouFullKernel y x * Real.exp ((s.re - 1 / 2) * x) by
    simp only [poitouTiltedFullKernel, norm_mul, norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (poitouFullKernel_nonneg y x),
      abs_of_pos (Real.exp_pos _)]
    ring ]
  have hg := poitouGaussian_le_one (poitouGaussianEpsilon_pos n).le x
  have hfull := poitouFullKernel_nonneg y x
  have hexp : Real.exp (((s - (1 / 2 : ℂ)) * (x : ℂ)).re) =
      Real.exp ((s.re - 1 / 2) * x) := by
    congr 1
    simp [Complex.mul_re, Complex.sub_re]
  rw [hexp]
  calc
    poitouFullKernel y x * poitouGaussian (poitouGaussianEpsilon n) x *
        Real.exp ((s.re - 1 / 2) * x) ≤
      poitouFullKernel y x * 1 * Real.exp ((s.re - 1 / 2) * x) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hg hfull) (Real.exp_pos _).le
    _ = poitouFullKernel y x * Real.exp ((s.re - 1 / 2) * x) := by ring

/-- The regularized zero transform tends to Poitou's original transform at
every point of the open critical strip. -/
theorem poitouGaussianRegularizedPhi_tendsto_poitouPhi
    {y : ℝ} (hy : 0 < y) (s : ℂ)
    (hs₁ : 0 < s.re) (hs₂ : s.re < 1) :
    Tendsto
      (fun n : ℕ ↦ poitouGaussianRegularizedPhi y (poitouGaussianEpsilon n) s)
      atTop (𝓝 (poitouPhi y s)) := by
  unfold poitouGaussianRegularizedPhi poitouPhi
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ ↦ ‖poitouTiltedFullKernel y (s.re - 1 / 2) x‖)
  · intro n
    exact ((Complex.continuous_ofReal.comp
      (poitouGaussianRegularizedKernel_continuous y (poitouGaussianEpsilon n))).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))).aestronglyMeasurable
  · exact (poitouTiltedFullKernel_integrable hy (by linarith) (by linarith)).norm
  · intro n
    filter_upwards with x
    exact poitouGaussianRegularizedPhi_integrand_norm_le n x
  · filter_upwards with x
    have hg := (poitouGaussian_epsilon_tendsto_one x).ofReal
    have hk : Tendsto
        (fun n : ℕ ↦
          (poitouGaussianRegularizedKernel y (poitouGaussianEpsilon n) x : ℂ))
        atTop (𝓝 (poitouFullKernel y x : ℂ)) := by
      simpa [poitouGaussianRegularizedKernel, Complex.ofReal_mul] using
        (tendsto_const_nhds.mul hg)
    exact hk.mul_const _

/-- The Gaussian-regularized endpoint integral tends to Poitou's exact
positive-half-line area. -/
theorem poitouGaussianRegularizedScaledTest_integral_Ioi_tendsto
    {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouGaussian (poitouGaussianEpsilon n) x)
      atTop (𝓝 (3 * Real.pi / (5 * Real.sqrt y))) := by
  have hDCT : Tendsto
      (fun n : ℕ ↦ ∫ x in Ioi (0 : ℝ),
        poitouScaledTest y x * poitouGaussian (poitouGaussianEpsilon n) x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), poitouScaledTest y x)) := by
    apply tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (fun x : ℝ ↦ poitouScaledTest y x)
    · intro n
      exact ((poitouScaledTest_continuous y).mul
        (poitouGaussian_continuous (poitouGaussianEpsilon n))).aestronglyMeasurable
    · exact (poitouScaledTest_integrable hy).integrableOn
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (poitouScaledTest_nonneg y x)
          (poitouGaussian_nonneg _ x))]
      exact mul_le_of_le_one_right (poitouScaledTest_nonneg y x)
        (poitouGaussian_le_one (poitouGaussianEpsilon_pos n).le x)
    · filter_upwards with x
      simpa using (tendsto_const_nhds.mul (poitouGaussian_epsilon_tendsto_one x))
  simpa only [poitouScaledTest_integral_Ioi hy] using hDCT

/-- Consequently the regularized endpoint correction tends to the exact
term `12π / (5 n √y)` in Poitou's formula. -/
theorem poitouGaussianRegularizedEndpointCorrection_tendsto
    (degree : ℕ) {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun n : ℕ ↦ 4 / (degree : ℝ) *
        (∫ x in Ioi (0 : ℝ),
          poitouScaledTest y x * poitouGaussian (poitouGaussianEpsilon n) x))
      atTop (𝓝 (12 * Real.pi / (5 * (degree : ℝ) * Real.sqrt y))) := by
  convert (poitouGaussianRegularizedScaledTest_integral_Ioi_tendsto hy).const_mul
    (4 / (degree : ℝ)) using 1
  congr 1
  ring

end
end TraceEuclidean.PoitouKernel
