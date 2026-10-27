import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Gaussian series on actual discrete lattices

The lattice is an arbitrary discrete integer submodule of a finite dimensional
real normed space. Gaussian summability is deduced from its proved power-series
bound, with no convergence or Poisson identity assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.LatticeGaussian

open Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The actual Gaussian sum, including its zero term. -/
def theta (t : ℝ) : ℝ := ∑' x : L, Real.exp (-t * ‖(x : E)‖ ^ 2)

/-- The same Gaussian series at a complex parameter. -/
def complexTheta (s : ℂ) : ℂ := ∑' x : L, Complex.exp (-s * (‖(x : E)‖ : ℂ) ^ 2)

/-- The ambient norm tends to infinity along the cofinite filter of a discrete lattice. -/
theorem norm_tendsto : Tendsto (fun x : L ↦ ‖(x : E)‖) cofinite atTop := by
  have hL : IsClosed (L : Set E) := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  exact tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
    hL.isClosedEmbedding_subtypeVal

/-- Every positive real Gaussian is summable on the actual lattice. -/
theorem summable (t : ℝ) (ht : 0 < t) :
    Summable (fun x : L ↦ Real.exp (-t * ‖(x : E)‖ ^ 2)) := by
  let r : ℝ := -(Module.finrank ℤ L : ℝ) - 1
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r]; linarith
  have h := (rexp_neg_quadratic_isLittleO_rpow_atTop (neg_neg_of_pos ht) 0 r).isBigO
    |>.comp_tendsto (norm_tendsto L)
  apply summable_of_isBigO (ZLattice.summable_norm_rpow L r hr)
  simpa [Function.comp_def] using h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The modulus of a complex Gaussian is exactly the real Gaussian at its real part. -/
theorem norm_complex_term (s : ℂ) (x : E) :
    ‖Complex.exp (-s * (‖x‖ : ℂ) ^ 2)‖ = Real.exp (-s.re * ‖x‖ ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

/-- The complex series is absolutely summable throughout the open right half-plane. -/
theorem norm_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun x : L ↦ ‖Complex.exp (-s * (‖(x : E)‖ : ℂ) ^ 2)‖) := by
  simpa only [norm_complex_term] using summable L s.re hs

/-- Actual complex Gaussian summability follows from the proved absolute convergence. -/
theorem complex_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun x : L ↦ Complex.exp (-s * (‖(x : E)‖ : ℂ) ^ 2)) :=
  (norm_summable L s hs).of_norm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Uniform domination on any closed right half-plane with positive boundary. -/
theorem norm_term_le (a : ℝ) (s : ℂ) (has : a ≤ s.re) (x : E) :
    ‖Complex.exp (-s * (‖x‖ : ℂ) ^ 2)‖ ≤ Real.exp (-a * ‖x‖ ^ 2) := by
  rw [norm_complex_term, Real.exp_le_exp]
  nlinarith [sq_nonneg ‖x‖]

/-- A basis-free Gaussian bound for the actual complex theta function. -/
theorem norm_theta_le (s : ℂ) (hs : 0 < s.re) :
    ‖complexTheta L s‖ ≤ theta L s.re := by
  simpa only [complexTheta, theta, norm_complex_term] using
    norm_tsum_le_tsum_norm (norm_summable L s hs)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- Restriction of the complex theta function to positive real parameters. -/
theorem complexTheta_ofReal (t : ℝ) : complexTheta L (t : ℂ) = (theta L t : ℂ) := by
  simp only [theta, complexTheta, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_tsum]

end NormEuclidean.LatticeGaussian
