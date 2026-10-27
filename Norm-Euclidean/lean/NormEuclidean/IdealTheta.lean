import NormEuclidean.LatticeThetaAnalytic
import NormEuclidean.LatticeThetaDecay
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Actual fractional-ideal theta functions

The mixed embedding is weighted by the square root of two at complex
places. Its Euclidean square norm is therefore the sum over all field
embeddings, with complex multiplicity two. Nonzero fractional ideals
are transported as actual discrete full lattices, not as free ideals
over the integer ring. The analytic results apply to their literal sums.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.IdealTheta

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open Filter Topology
open scoped NumberField Classical nonZeroDivisors

variable (F : Type*) [Field F] [NumberField F]

/-- Multiply complex coordinates by the square root of their trace multiplicity. -/
def weight : mixedSpace F ≃L[ℝ] mixedSpace F :=
  (ContinuousLinearEquiv.refl ℝ _).prodCongr
    ((LinearEquiv.smulOfUnit (M := {w : InfinitePlace F // IsComplex w} → ℂ)
      (Units.mk0 (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num)).ne')).toContinuousLinearEquiv)

/-- Actual trace-normalized Euclidean coordinates on the mixed space. -/
def euclidean : mixedSpace F ≃L[ℝ] mixedEmbedding.euclidean.mixedSpace F :=
  (weight F).trans (mixedEmbedding.euclidean.toMixed F).symm

/-- The weighted image of an actual field element. -/
def embedding (x : F) : mixedEmbedding.euclidean.mixedSpace F :=
  euclidean F (mixedEmbedding F x)

/-- The actual nonzero fractional ideal, transported into its weighted Euclidean space. -/
def lattice (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace F) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice F I) (euclidean F).symm.toLinearMap

instance lattice_discrete (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    DiscreteTopology (lattice F I) := by unfold lattice; infer_instance

instance lattice_full (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : IsZLattice ℝ (lattice F I) := by
  unfold lattice
  infer_instance

/-- Membership is established from the original fractional ideal membership. -/
theorem embedding_mem (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (x : F) (hx : x ∈ (I : Set F)) :
    embedding F x ∈ lattice F I := by
  change (euclidean F).symm (euclidean F (mixedEmbedding F x)) ∈ idealLattice F I
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact (mem_idealLattice F I).mpr ⟨x, hx, rfl⟩

/-- A proved bijection identifies original ideal elements and actual lattice vectors. -/
def idealEquiv (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    {x : F // x ∈ (I : Set F)} ≃ lattice F I :=
  Equiv.ofBijective (fun x ↦ ⟨embedding F x.1, embedding_mem F I x.1 x.2⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext ((mixedEmbedding_injective F)
        ((euclidean F).injective (congrArg Subtype.val h)))
    · intro y
      obtain ⟨x, hx, hxy⟩ := (mem_idealLattice F I).mp y.2
      change mixedEmbedding F x = (euclidean F).symm (y : _) at hxy
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      change euclidean F (mixedEmbedding F x) = (y : mixedEmbedding.euclidean.mixedSpace F)
      rw [hxy, ContinuousLinearEquiv.apply_symm_apply])

@[simp]
theorem idealEquiv_apply (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : Set F)}) :
    (idealEquiv F I x : mixedEmbedding.euclidean.mixedSpace F) = embedding F x := rfl

@[simp]
theorem idealEquiv_norm (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : Set F)}) : ‖idealEquiv F I x‖ = ‖embedding F x‖ := rfl

/-- The literal ideal theta sum uses its original ideal elements as indices. -/
def theta (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) : ℝ :=
  ∑' x : {x : F // x ∈ (I : Set F)}, Real.exp (-Real.pi * t * ‖embedding F x‖ ^ 2)

/-- The same literal ideal sum with a complex Gaussian parameter. -/
def complexTheta (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℂ) : ℂ :=
  ∑' x : {x : F // x ∈ (I : Set F)},
    Complex.exp (-Real.pi * s * (‖embedding F x‖ : ℂ) ^ 2)

/-- Reindexing is a theorem about the original ideal sum and the proved lattice model. -/
theorem theta_eq (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) :
    theta F I t = LatticeGaussian.theta (lattice F I) (Real.pi * t) := by
  unfold theta LatticeGaussian.theta
  rw [← (idealEquiv F I).tsum_eq
    (fun y : lattice F I ↦ Real.exp (-(Real.pi * t) *
      ‖(y : mixedEmbedding.euclidean.mixedSpace F)‖ ^ 2))]
  apply tsum_congr
  intro x
  change Real.exp (-Real.pi * t * ‖embedding F x‖ ^ 2) =
    Real.exp (-(Real.pi * t) * ‖embedding F x‖ ^ 2)
  congr 1
  ring

/-- Complex reindexing likewise identifies the actual Gaussian series. -/
theorem complexTheta_eq (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℂ) :
    complexTheta F I s = LatticeGaussian.complexTheta (lattice F I) (Real.pi * s) := by
  unfold complexTheta LatticeGaussian.complexTheta
  rw [← (idealEquiv F I).tsum_eq
    (fun y : lattice F I ↦ Complex.exp (-(Real.pi * s) *
      (‖(y : mixedEmbedding.euclidean.mixedSpace F)‖ : ℂ) ^ 2))]
  apply tsum_congr
  intro x
  change Complex.exp (-Real.pi * s * (‖embedding F x‖ : ℂ) ^ 2) =
    Complex.exp (-(Real.pi * s) * (‖embedding F x‖ : ℂ) ^ 2)
  congr 1
  ring

/-- Absolute convergence holds on the actual original ideal, with no ideal freeness assumption. -/
theorem summable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    Summable (fun x : {x : F // x ∈ (I : Set F)} ↦
      Real.exp (-Real.pi * t * ‖embedding F x‖ ^ 2)) := by
  have h := (LatticeGaussian.summable (lattice F I) (Real.pi * t)
    (mul_pos Real.pi_pos ht)).comp_injective (idealEquiv F I).injective
  apply h.congr
  intro x
  change Real.exp (-(Real.pi * t) * ‖embedding F x‖ ^ 2) =
    Real.exp (-Real.pi * t * ‖embedding F x‖ ^ 2)
  congr 1
  ring

/-- Absolute convergence is proved on the original ideal at every positive-real-part parameter. -/
theorem complex_norm_summable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℂ) (hs : 0 < s.re) :
    Summable (fun x : {x : F // x ∈ (I : Set F)} ↦
      ‖Complex.exp (-Real.pi * s * (‖embedding F x‖ : ℂ) ^ 2)‖) := by
  have hpos : 0 < ((Real.pi : ℂ) * s).re := by
    simpa only [Complex.re_ofReal_mul] using mul_pos Real.pi_pos hs
  have h := (LatticeGaussian.norm_summable (lattice F I) (Real.pi * s) hpos)
    |>.comp_injective (idealEquiv F I).injective
  apply h.congr
  intro x
  change ‖Complex.exp (-(Real.pi * s) * (‖embedding F x‖ : ℂ) ^ 2)‖ =
    ‖Complex.exp (-Real.pi * s * (‖embedding F x‖ : ℂ) ^ 2)‖
  apply congrArg (fun z : ℂ ↦ ‖Complex.exp z‖)
  ring

/-- In particular the original complex ideal series has an actual sum in that half-plane. -/
theorem complex_summable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℂ) (hs : 0 < s.re) :
    Summable (fun x : {x : F // x ∈ (I : Set F)} ↦
      Complex.exp (-Real.pi * s * (‖embedding F x‖ : ℂ) ^ 2)) :=
  (complex_norm_summable F I s hs).of_norm

/-- The actual theta sum is holomorphic in the open right half-plane. -/
theorem analyticAt (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (complexTheta F I) s := by
  have he : complexTheta F I =
      fun z ↦ LatticeGaussian.complexTheta (lattice F I) (Real.pi * z) :=
    funext (complexTheta_eq F I)
  rw [he]
  apply (LatticeThetaAnalytic.analyticAt (lattice F I) (Real.pi * s) ?_).comp
    (analyticAt_const.mul analyticAt_id)
  simpa only [Complex.re_ofReal_mul] using mul_pos Real.pi_pos hs

/-- The ideal theta sum has its actual zero vector and is at least one. -/
theorem one_le_theta (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    1 ≤ theta F I t := by
  rw [theta_eq]
  exact LatticeThetaDecay.one_le_theta _ _ (mul_pos Real.pi_pos ht)

/-- Every actual fractional-ideal theta function tends to one at positive infinity. -/
theorem tendsto_theta (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Tendsto (theta F I) atTop (𝓝 1) := by
  have h := (LatticeThetaDecay.tendsto_theta (lattice F I)).comp
    (tendsto_id.const_mul_atTop Real.pi_pos)
  simpa only [Function.comp_def, id_eq, ← theta_eq] using h

end NormEuclidean.IdealTheta
