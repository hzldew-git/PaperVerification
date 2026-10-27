import NormEuclidean.ChapterX.PseudoBasisVolume
import NormEuclidean.ChapterX.VolumeFiniteness

/-!
# Uniform absolute volume-norm bounds

The actual finite interval of volume ideals supplies a uniform absolute norm
bound. In the actual pseudobasis this is a Gram-norm times coefficient-norm
bound. A Minkowski small-vector existence theorem is still a separate input.
-/

noncomputable section

namespace NormEuclidean.VolumeNormBound

open Module IntegralVolume
open scoped NumberField nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- Integral-scale lattices above a fixed nonzero volume ideal have uniformly
bounded actual absolute volume norm. This does not assert class finiteness. -/
theorem exists_norm_bound (Q : QuadraticForm K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    ∃ C : ℚ, 0 ≤ C ∧ ∀ L : Lattice (integerSubring K) Q,
      L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal → FractionalIdeal.absNorm L.volumeIdeal ≤ C := by
  classical
  let E : Set (FractionalIdeal (integerSubring K)⁰ K) :=
    {I | ∃ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 ∧ c ≤ L.volumeIdeal ∧
      L.volumeIdeal = I}
  have hE : E.Finite := finite_volumeIdeals_of_lower_bound Q c hc
  obtain ⟨C, hC⟩ := (hE.image FractionalIdeal.absNorm).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro L hs hvol
  exact (hC ⟨L.volumeIdeal, ⟨L, hs, hvol, rfl⟩, rfl⟩).trans (le_max_left _ _)

/-- The same bound controls the actual pseudobasis Gram and coefficient norms.
No chosen integral basis, total reality or positivity is required. -/
theorem exists_pseudobasis_norm_bound (Q : QuadraticForm K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    ∃ C : ℚ, 0 ≤ C ∧ ∀ L : Lattice (integerSubring K) Q,
      L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
        ∃ b : Basis (Fin (Module.finrank K V)) K V,
          ∃ I : Fin (Module.finrank K V) → FractionalIdeal (integerSubring K)⁰ K,
            (∀ i, I i ≠ 0) ∧ (∀ x : V, x ∈ L.carrier ↔ ∀ i, b.repr x i ∈ I i) ∧
              fieldAbsNorm K (pairingMatrix (halfPolar Q) b b).det *
                (∏ i, FractionalIdeal.absNorm (I i)) ^ 2 ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_bound Q c hc
  refine ⟨C, hC, ?_⟩
  intro L hs hvol
  obtain ⟨b, I, hI, hmem, _, hnorm⟩ :=
    PseudoBasisVolume.exists_volume_formula_with_norm (halfPolar Q) L.carrier L.finite L.full
  refine ⟨b, I, hI, hmem, ?_⟩
  rw [← hnorm]
  exact hbound L hs hvol

end NormEuclidean.VolumeNormBound
