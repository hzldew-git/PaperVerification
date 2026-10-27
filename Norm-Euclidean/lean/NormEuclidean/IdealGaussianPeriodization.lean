import NormEuclidean.LatticeGaussianPeriodization
import NormEuclidean.IdealThetaNormalization

/-!
# Continuous periodization of the actual ideal trace Gaussian

The sum remains indexed by the original nonzero fractional ideal.
Actual Euclidean lattice transport proves convergence, continuity and
ideal-translation invariance. Diagonal Gaussian evaluation identifies
the summands with the previously fixed infinite trace Fourier Gaussian.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.IdealGaussianPeriodization

open NumberField NumberField.mixedEmbedding Filter Topology MeasureTheory
open scoped NumberField Classical nonZeroDivisors

variable (F : Type*) [Field F] [NumberField F]

/-- The literal ideal-indexed trace Gaussian summed over actual lattice translates. -/
def periodization (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (x : mixedSpace F) : ℝ :=
  ∑' a : {a : F // a ∈ (I : Set F)},
    Real.exp (-Real.pi * t * ‖IdealTheta.euclidean F (x + mixedEmbedding F a)‖ ^ 2)

/-- A proved reindexing compares the original periodization with its actual Euclidean lattice. -/
theorem eq_lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (x : mixedSpace F) :
    periodization F I t x = LatticeGaussianPeriodization.periodization
      (IdealTheta.lattice F I) (Real.pi * t) (IdealTheta.euclidean F x) := by
  unfold periodization LatticeGaussianPeriodization.periodization
  rw [← (IdealTheta.idealEquiv F I).tsum_eq (fun a : IdealTheta.lattice F I ↦
    Real.exp (-(Real.pi * t) * ‖IdealTheta.euclidean F x +
      (a : mixedEmbedding.euclidean.mixedSpace F)‖ ^ 2))]
  apply tsum_congr
  intro a
  change Real.exp (-Real.pi * t *
    ‖IdealTheta.euclidean F (x + mixedEmbedding F a)‖ ^ 2) =
    Real.exp (-(Real.pi * t) *
      ‖IdealTheta.euclidean F x + IdealTheta.embedding F a‖ ^ 2)
  rw [map_add]
  apply congrArg Real.exp
  unfold IdealTheta.embedding
  ring

/-- Actual summability holds for every shift, without a convergence premise. -/
theorem summable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t)
    (x : mixedSpace F) : Summable (fun a : {a : F // a ∈ (I : Set F)} ↦
      Real.exp (-Real.pi * t * ‖IdealTheta.euclidean F (x + mixedEmbedding F a)‖ ^ 2)) := by
  have h := (LatticeGaussianPeriodization.summable (IdealTheta.lattice F I) (Real.pi * t)
    (mul_pos Real.pi_pos ht) (IdealTheta.euclidean F x)).comp_injective
      (IdealTheta.idealEquiv F I).injective
  apply h.congr
  intro a
  change Real.exp (-(Real.pi * t) *
    ‖IdealTheta.euclidean F x + IdealTheta.embedding F a‖ ^ 2) =
    Real.exp (-Real.pi * t * ‖IdealTheta.euclidean F (x + mixedEmbedding F a)‖ ^ 2)
  rw [map_add]
  apply congrArg Real.exp
  unfold IdealTheta.embedding
  ring

/-- The literal original-ideal sum is a continuous function of the mixed translation. -/
theorem continuous (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    Continuous (periodization F I t) := by
  have he : periodization F I t = fun x ↦ LatticeGaussianPeriodization.periodization
      (IdealTheta.lattice F I) (Real.pi * t) (IdealTheta.euclidean F x) :=
    funext (eq_lattice F I t)
  rw [he]
  exact (LatticeGaussianPeriodization.continuous _ _ (mul_pos Real.pi_pos ht)).comp
    (IdealTheta.euclidean F).continuous

/-- Original ideal translation invariance follows from actual lattice reindexing. -/
theorem add_ideal (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (x : mixedSpace F)
    (a : F) (ha : a ∈ (I : Set F)) :
    periodization F I t (x + mixedEmbedding F a) = periodization F I t x := by
  rw [eq_lattice, eq_lattice, map_add]
  exact LatticeGaussianPeriodization.add_lattice (IdealTheta.lattice F I) (Real.pi * t)
    (IdealTheta.euclidean F x) ⟨IdealTheta.embedding F a, IdealTheta.embedding_mem F I a ha⟩

/-- The actual theta function is the value of this continuous periodization at zero. -/
theorem zero (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) :
    periodization F I t 0 = IdealTheta.theta F I t := by
  simp only [periodization, IdealTheta.theta, zero_add, IdealTheta.embedding]

/-- Individual translated summands are the original infinite trace Gaussian. -/
theorem gaussian_translate (t : ℝ) (x : mixedSpace F) (a : F) :
    TraceGaussianFourier.gaussian F t
        ((InfiniteTraceHaar.coordinates F).symm x + algebraMap F (InfiniteAdeleRing F) a) =
      (Real.exp (-Real.pi * t *
        ‖IdealTheta.euclidean F (x + mixedEmbedding F a)‖ ^ 2) : ℂ) := by
  rw [IdealThetaNormalization.gaussian_eq_exp, map_add,
    ContinuousAddEquiv.apply_symm_apply, InfiniteTraceHaar.coordinates_diagonal,
    ← IdealThetaNormalization.euclidean_norm_sq]
  push_cast
  rfl

/-- The original periodization is exactly the sum of actual translated adelic Gaussians. -/
theorem eq_gaussian_sum (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (x : mixedSpace F) :
    (periodization F I t x : ℂ) = ∑' a : {a : F // a ∈ (I : Set F)},
      TraceGaussianFourier.gaussian F t
        ((InfiniteTraceHaar.coordinates F).symm x + algebraMap F (InfiniteAdeleRing F) a.1) := by
  simp only [periodization, Complex.ofReal_tsum, gaussian_translate]

end NormEuclidean.IdealGaussianPeriodization
