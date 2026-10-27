import NormEuclidean.PositiveVolumeValues
import NormEuclidean.ChapterX.VolumeFiniteness

/-!
# A finite ideal envelope for a numerical volume bound in arbitrary rank

Doubling makes the half-polar volume integral. Its absolute norm is multiplied
by exactly `2^(n*[K:Q])`. Dividing the resulting finite ideal set by this fixed
principal ideal recovers the original, possibly fractional, volume ideals.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.BoundedVolumeIdeals

open Module
open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))
local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

def doublingFactor (n : ℕ) : FractionalIdeal (integerSubring K)⁰ K :=
  FractionalIdeal.spanSingleton (integerSubring K)⁰ ((2 : K) ^ n)

theorem doublingFactor_ne_zero (n : ℕ) : doublingFactor (K := K) n ≠ 0 :=
  FractionalIdeal.spanSingleton_ne_zero_iff.mpr (pow_ne_zero _ (by norm_num))

theorem doublingFactor_norm (n : ℕ) :
    FractionalIdeal.absNorm (doublingFactor (K := K) n) =
      (2 : ℚ) ^ (n * finrank ℚ K) := by
  rw [doublingFactor, FractionalIdeal.absNorm_span_singleton, map_pow]
  have htwo : Algebra.norm ℚ (2 : K) = (2 : ℚ) ^ finrank ℚ K :=
    Algebra.norm_natCast ℚ 2
  rw [htwo, ← pow_mul, Nat.mul_comm]
  exact abs_of_nonneg (by positivity)

universe v

/-- The finite ideal set is chosen solely from the field, rank and real
volume bound, before choosing any ambient quadratic space or lattice. -/
theorem exists_finite_ideals (n : ℕ) (C : ℝ) :
    ∃ S : Set (FractionalIdeal (integerSubring K)⁰ K), S.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), finrank K V = n →
        (FractionalIdeal.absNorm L.volumeIdeal : ℝ) ≤ C → L.volumeIdeal ∈ S := by
  let f := doublingFactor (K := K) n
  let D := (2 : ℝ) ^ (n * finrank ℚ K) * C
  let T := {I : Ideal (integerSubring K) | Ideal.absNorm I ≤ ⌈D⌉₊}
  have hT : T.Finite := Ideal.finite_setOf_absNorm_le ⌈D⌉₊
  refine ⟨(fun I : Ideal (integerSubring K) ↦
    (I : FractionalIdeal (integerSubring K)⁰ K) / f) '' T,
    hT.image _, ?_⟩
  intro V _ _ Q L hr hvol
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    ((L.rescale 2).volumeIdeal_le_one L.doubled_scaleIdeal_le_one)
  have hvol2 : (L.rescale 2).volumeIdeal = f * L.volumeIdeal := by
    rw [L.volumeIdeal_rescale, hr]
    rfl
  have hNI : (Ideal.absNorm I : ℝ) =
      (2 : ℝ) ^ (n * finrank ℚ K) * FractionalIdeal.absNorm L.volumeIdeal := by
    have h := congrArg FractionalIdeal.absNorm hI
    rw [FractionalIdeal.coeIdeal_absNorm, hvol2, map_mul, doublingFactor_norm] at h
    exact_mod_cast h
  have hbound : (Ideal.absNorm I : ℝ) ≤ D := by
    rw [hNI]
    exact mul_le_mul_of_nonneg_left hvol (by positivity)
  refine ⟨I, ?_, ?_⟩
  · exact_mod_cast hbound.trans (Nat.le_ceil D)
  · apply (div_eq_iff (doublingFactor_ne_zero n)).mpr
    rw [hI, hvol2, mul_comm]

end NormEuclidean.BoundedVolumeIdeals
