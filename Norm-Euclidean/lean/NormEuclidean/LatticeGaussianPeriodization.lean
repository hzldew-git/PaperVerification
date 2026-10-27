import NormEuclidean.LatticeGaussian
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Actual Gaussian periodization on a discrete lattice

A uniform shifted-Gaussian estimate proves convergence on bounded
sets. The original lattice sum is continuous and invariant under
translation by actual lattice vectors. No Fourier inversion or
Poisson identity is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.LatticeGaussianPeriodization

open Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The literal periodized Gaussian over all actual lattice vectors. -/
def periodization (t : ℝ) (x : E) : ℝ :=
  ∑' y : L, Real.exp (-t * ‖x + (y : E)‖ ^ 2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A quadratic bound for a translated norm, valid for any real normed space. -/
theorem norm_sq_bound (x y : E) : ‖y‖ ^ 2 ≤ 2 * (‖x + y‖ ^ 2 + ‖x‖ ^ 2) := by
  have h : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (x + y) x
  have hh := (sq_le_sq₀ (norm_nonneg y) (by positivity : 0 ≤ ‖x + y‖ + ‖x‖)).mpr h
  nlinarith [sq_nonneg (‖x + y‖ - ‖x‖)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A single summable Gaussian dominates all translates in a fixed norm ball. -/
theorem term_le (t : ℝ) (ht : 0 < t) (R : ℝ) (x y : E) (hx : ‖x‖ ≤ R) :
    Real.exp (-t * ‖x + y‖ ^ 2) ≤
      Real.exp (t * R ^ 2) * Real.exp (-(t / 2) * ‖y‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg x) hR).mpr hx
  have hn := norm_sq_bound x y
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hsq),
    mul_nonneg ht.le (sub_nonneg.mpr hn)]

/-- Actual absolute convergence at every translation parameter. -/
theorem summable (t : ℝ) (ht : 0 < t) (x : E) :
    Summable (fun y : L ↦ Real.exp (-t * ‖x + (y : E)‖ ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
    (fun y : L ↦ term_le t ht ‖x‖ x (y : E) le_rfl)
    ((LatticeGaussian.summable L (t / 2) (half_pos ht)).mul_left _)

/-- Uniform convergence on any fixed norm ball follows from a proved summable majorant. -/
theorem hasSum_uniformly (t : ℝ) (ht : 0 < t) (R : ℝ) :
    HasSumUniformlyOn (fun y : L ↦ fun x : E ↦ Real.exp (-t * ‖x + (y : E)‖ ^ 2))
      (periodization L t) (closedBall 0 R) := by
  apply HasSumUniformlyOn.of_norm_le_summable
    ((LatticeGaussian.summable L (t / 2) (half_pos ht)).mul_left (Real.exp (t * R ^ 2)))
  intro y x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact term_le t ht R x y (by simpa only [mem_closedBall_zero_iff] using hx)

/-- The actual lattice periodization is continuous on each norm ball. -/
theorem continuousOn (t : ℝ) (ht : 0 < t) (R : ℝ) :
    ContinuousOn (periodization L t) (closedBall 0 R) := by
  apply (hasSum_uniformly L t ht R).tendstoUniformlyOn.continuousOn
  apply Filter.Eventually.frequently
  filter_upwards with s
  exact continuousOn_finsetSum _ (fun _ _ ↦ by fun_prop)

/-- In particular it is an actual continuous function on the entire ambient space. -/
theorem continuous (t : ℝ) (ht : 0 < t) : Continuous (periodization L t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (continuousOn L t ht (‖x‖ + 1)).continuousAt
  apply closedBall_mem_nhds_of_mem
  rw [mem_ball, dist_zero_right]
  exact lt_add_one ‖x‖

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- Translation by an original lattice vector leaves the actual series unchanged. -/
theorem add_lattice (t : ℝ) (x : E) (a : L) :
    periodization L t (x + (a : E)) = periodization L t x := by
  have h := (Equiv.addLeft a).tsum_eq
    (fun y : L ↦ Real.exp (-t * ‖x + (y : E)‖ ^ 2))
  change (∑' y : L, Real.exp (-t * ‖x + ((a : E) + (y : E))‖ ^ 2)) =
    ∑' y : L, Real.exp (-t * ‖x + (y : E)‖ ^ 2) at h
  simpa only [periodization, add_assoc] using h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- Evaluation at zero is the already constructed original theta sum. -/
theorem zero (t : ℝ) : periodization L t 0 = LatticeGaussian.theta L t := by
  simp only [periodization, zero_add, LatticeGaussian.theta]

end NormEuclidean.LatticeGaussianPeriodization
