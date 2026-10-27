import NormEuclidean.LatticeGaussian
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphy of the actual lattice Gaussian series

A summable Gaussian at a positive real parameter dominates every term
on the corresponding closed right half-plane. This proves locally
uniform convergence and holomorphy of the actual series, rather than
postulating an analytic function with prescribed theta values.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.LatticeThetaAnalytic

open Filter Topology Set LatticeGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The actual partial sums converge uniformly on every positive closed right half-plane. -/
theorem hasSum_uniformly (a : ℝ) (ha : 0 < a) :
    HasSumUniformlyOn
      (fun x : L ↦ fun s : ℂ ↦ Complex.exp (-s * (‖(x : E)‖ : ℂ) ^ 2))
      (complexTheta L) {s : ℂ | a ≤ s.re} :=
  HasSumUniformlyOn.of_norm_le_summable (LatticeGaussian.summable L a ha)
    (fun x s hs ↦ norm_term_le a s hs (x : E))

/-- Local uniform convergence holds throughout the natural right half-plane of the theta sum. -/
theorem hasSum_locallyUniformly :
    HasSumLocallyUniformlyOn
      (fun x : L ↦ fun s : ℂ ↦ Complex.exp (-s * (‖(x : E)‖ : ℂ) ^ 2))
      (complexTheta L) {s : ℂ | 0 < s.re} := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  change 0 < z.re at hz
  let a := z.re / 2
  have ha : 0 < a := by dsimp [a]; exact half_pos hz
  refine ⟨{s : ℂ | a < s.re}, ?_, ?_⟩
  · apply mem_nhdsWithin_of_mem_nhds
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    change z.re / 2 < z.re
    linarith
  · exact (hasSum_uniformly L a ha).mono (fun s h ↦ (show a < s.re from h).le)

/-- The actual Gaussian sum is complex differentiable on its open half-plane. -/
theorem differentiableOn :
    DifferentiableOn ℂ (complexTheta L) {s : ℂ | 0 < s.re} := by
  apply (hasSum_locallyUniformly L).summableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
  intro x s _
  fun_prop

/-- Consequently the theta series is holomorphic near every point of that half-plane. -/
theorem analyticOnNhd : AnalyticOnNhd ℂ (complexTheta L) {s : ℂ | 0 < s.re} :=
  (differentiableOn L).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- Holomorphy is a proved property of the original sum at an individual parameter. -/
theorem analyticAt (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (complexTheta L) s :=
  analyticOnNhd L s hs

/-- The real theta function is continuous at every positive parameter. -/
theorem continuousAt_theta (t : ℝ) (ht : 0 < t) : ContinuousAt (theta L) t := by
  have hc := Complex.continuous_re.continuousAt.comp
    ((analyticAt L t ht).continuousAt.comp Complex.continuous_ofReal.continuousAt)
  simpa only [Function.comp_def, complexTheta_ofReal, Complex.ofReal_re] using hc

end NormEuclidean.LatticeThetaAnalytic
