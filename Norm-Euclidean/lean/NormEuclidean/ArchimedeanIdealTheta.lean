import NormEuclidean.UnitLogShape

/-!
# Actual ideal theta functions with independent infinite-place scalings

The indices remain the original fractional-ideal elements. A uniform
Gaussian majorant on every bounded logarithmic parameter set proves
absolute convergence and continuity, without a convergence premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace NormEuclidean.ArchimedeanIdealTheta

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open ArchimedeanLogScale IdealThetaNormalization Metric Filter Topology
open scoped NumberField Classical nonZeroDivisors

variable (F : Type*) [Field F] [NumberField F]

/-- The original Gaussian energy has a positive uniform lower bound on every log box. -/
theorem energy_lower (c : ℝ) (r : InfinitePlace F → ℝ)
    (hr : ∀ w, c ≤ r w) (x : mixedSpace F) :
    Real.exp c ^ 2 * ‖IdealTheta.euclidean F x‖ ^ 2 ≤
      ‖IdealTheta.euclidean F (scale F r x)‖ ^ 2 := by
  rw [ArchimedeanLogScale.energy, euclidean_norm_sq]
  have he (w : InfinitePlace F) : Real.exp c ^ 2 ≤ Real.exp (r w) ^ 2 :=
    (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).mpr
      (Real.exp_le_exp.mpr (hr w))
  unfold IdealThetaNormalization.energy
  calc
    _ = (∑ w : {w : InfinitePlace F // IsReal w}, Real.exp c ^ 2 * (x.1 w) ^ 2) +
        2 * ∑ w : {w : InfinitePlace F // IsComplex w},
          Real.exp c ^ 2 * ‖x.2 w‖ ^ 2 := by
      simp only [← Finset.mul_sum]
      ring
    _ ≤ _ := add_le_add
      (Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_right (he w) (sq_nonneg _))
      (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_right (he w) (sq_nonneg _))
        (by norm_num))

/-- The literal scaled theta sum over the original actual fractional ideal. -/
def theta (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (r : InfinitePlace F → ℝ) : ℝ :=
  ∑' x : {x : F // x ∈ (I : Set F)},
    Real.exp (-Real.pi * t *
      ‖IdealTheta.euclidean F (scale F r (mixedEmbedding F x))‖ ^ 2)

/-- The zero shape recovers the already proved original ideal theta series. -/
theorem zero (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) :
    theta F I t 0 = IdealTheta.theta F I t := by
  simp only [theta, scale_zero, IdealTheta.theta, IdealTheta.embedding]

/-- A single original-ideal Gaussian dominates all logarithmic parameters in a norm ball. -/
theorem term_le (t : ℝ) (ht : 0 < t) (R : ℝ) (r : InfinitePlace F → ℝ)
    (hr : ‖r‖ ≤ R) (x : F) :
    Real.exp (-Real.pi * t *
      ‖IdealTheta.euclidean F (scale F r (mixedEmbedding F x))‖ ^ 2) ≤
        Real.exp (-Real.pi * (t * Real.exp (-R) ^ 2) * ‖IdealTheta.embedding F x‖ ^ 2) := by
  have hl (w : InfinitePlace F) : -R ≤ r w :=
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm r w).trans hr)).1
  have he := energy_lower F (-R) r hl (mixedEmbedding F x)
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left he (mul_pos Real.pi_pos ht).le
  change Real.pi * t * (Real.exp (-R) ^ 2 * ‖IdealTheta.embedding F x‖ ^ 2) ≤ _ at hh
  nlinarith

/-- Actual absolute convergence holds at every shape and every positive real radial parameter. -/
theorem summable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t)
    (r : InfinitePlace F → ℝ) :
    Summable (fun x : {x : F // x ∈ (I : Set F)} ↦
      Real.exp (-Real.pi * t *
        ‖IdealTheta.euclidean F (scale F r (mixedEmbedding F x))‖ ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
    (fun x : {x : F // x ∈ (I : Set F)} ↦ term_le F t ht ‖r‖ r le_rfl x)
    (IdealTheta.summable F I (t * Real.exp (-‖r‖) ^ 2) (by positivity))

/-- Every original Gaussian summand is continuous in all actual log-place coordinates. -/
theorem continuous_term (t : ℝ) (x : F) :
    Continuous (fun r : InfinitePlace F → ℝ ↦
      Real.exp (-Real.pi * t *
        ‖IdealTheta.euclidean F (scale F r (mixedEmbedding F x))‖ ^ 2)) := by
  have hp : Continuous (fun r : InfinitePlace F → ℝ ↦ (r, mixedEmbedding F x)) :=
    continuous_id.prodMk continuous_const
  have hs := (ArchimedeanLogScale.continuous F).comp hp
  have he : Continuous (fun r : InfinitePlace F → ℝ ↦
      ‖IdealTheta.euclidean F (scale F r (mixedEmbedding F x))‖ ^ 2) :=
    ((IdealTheta.euclidean F).continuous.comp hs).norm.pow 2
  exact Real.continuous_exp.comp (continuous_const.mul he)

/-- Actual partial sums converge uniformly on every bounded closed log-parameter ball. -/
theorem hasSum_uniformly (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : ℝ) (ht : 0 < t) (R : ℝ) :
    HasSumUniformlyOn
      (fun x : {x : F // x ∈ (I : Set F)} ↦ fun r : InfinitePlace F → ℝ ↦
        Real.exp (-Real.pi * t *
          ‖IdealTheta.euclidean F (scale F r (mixedEmbedding F x))‖ ^ 2))
      (theta F I t) (closedBall 0 R) := by
  apply HasSumUniformlyOn.of_norm_le_summable
    (IdealTheta.summable F I (t * Real.exp (-R) ^ 2) (by positivity))
  intro x r hr
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact term_le F t ht R r (by simpa only [mem_closedBall_zero_iff] using hr) x

/-- The actual original-ideal theta sum is continuous in all infinite-place shapes. -/
theorem continuous (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    Continuous (theta F I t) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  have hc : ContinuousOn (theta F I t) (closedBall 0 (‖r‖ + 1)) := by
    apply (hasSum_uniformly F I t ht (‖r‖ + 1)).tendstoUniformlyOn.continuousOn
    apply Filter.Eventually.frequently
    filter_upwards with s
    exact continuousOn_finsetSum _ (fun x _ ↦ (continuous_term F t x).continuousOn)
  apply hc.continuousAt
  apply closedBall_mem_nhds_of_mem
  rw [mem_ball, dist_zero_right]
  exact lt_add_one ‖r‖

end NormEuclidean.ArchimedeanIdealTheta
