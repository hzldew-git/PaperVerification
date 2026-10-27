import NormEuclidean.ChapterX.IdealClassRepresentatives
import NormEuclidean.ChapterX.VolumeFiniteness

/-!
# A common integral scalar for bounded products of ideal pairs

For nonzero fractional ideals `I,J` with `c <= I*J <= 1`, one fixed nonzero
integer can be split as `t*beta` in `I` and `beta/t` in `J`. Actual finite
ideal classes and the actual finite ideal interval construct this scalar.
-/

noncomputable section

namespace NormEuclidean.UniformIdealPair

open IdealClassRepresentatives
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Bounded products of arbitrary nonzero fractional ideal pairs admit one
common nonzero integral scalar, after a pair-dependent principal adjustment. -/
theorem exists_common_scalar (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    ∃ β : integerSubring K, β ≠ 0 ∧
      ∀ I J : FractionalIdeal (integerSubring K)⁰ K, I ≠ 0 → J ≠ 0 →
        c ≤ I * J → I * J ≤ 1 →
          ∃ t : K, t ≠ 0 ∧ t * (β : K) ∈ I ∧ (β : K) / t ∈ J := by
  classical
  obtain ⟨s, hs, hrep⟩ := exists_finite_representatives (K := K)
  let E : Set (FractionalIdeal (integerSubring K)⁰ K) := {D | c ≤ D ∧ D ≤ 1}
  have hE := IntegralVolume.finite_integral_ideals_containing c hc
  let d := hE.toFinset
  let p := (d ×ˢ s).image fun q ↦ q.1 * q.2⁻¹
  have hp : ∀ J ∈ s ∪ p, J ≠ 0 := by
    intro J hJ
    rcases Finset.mem_union.mp hJ with hJ | hJ
    · exact hs J hJ
    · obtain ⟨⟨D, A⟩, hDA, rfl⟩ := Finset.mem_image.mp hJ
      obtain ⟨hD, hA⟩ := Finset.mem_product.mp hDA
      have hDc : c ≤ D := (hE.mem_toFinset.mp hD).1
      have hD0 : D ≠ 0 := by
        intro h
        apply hc
        apply le_antisymm
        · simpa only [h] using hDc
        · exact bot_le
      exact mul_ne_zero hD0 (inv_ne_zero (hs A hA))
  obtain ⟨β, hβ, hβall⟩ := exists_common_nonzero_integer (s ∪ p) hp
  refine ⟨β, hβ, ?_⟩
  intro I J hI _ hlow hupp
  obtain ⟨A, hA, t, ht, hIA⟩ := hrep I hI
  have hβA : (β : K) ∈ A := hβall A (Finset.mem_union_left _ hA)
  have hβD : (β : K) ∈ (I * J) * A⁻¹ := by
    apply hβall _ (Finset.mem_union_right _ (Finset.mem_image.mpr ?_))
    exact ⟨(I * J, A), Finset.mem_product.mpr
      ⟨hE.mem_toFinset.mpr ⟨hlow, hupp⟩, hA⟩, rfl⟩
  have hDA : (I * J) * A⁻¹ = FractionalIdeal.spanSingleton (integerSubring K)⁰ t * J := by
    rw [hIA]
    calc
      ((FractionalIdeal.spanSingleton (integerSubring K)⁰ t * A) * J) * A⁻¹ =
          (FractionalIdeal.spanSingleton (integerSubring K)⁰ t * J) * (A * A⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ (hs A hA), mul_one]
  rw [hDA] at hβD
  obtain ⟨a, ha, hβa⟩ := FractionalIdeal.mem_singleton_mul.mp hβD
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hIA]
    exact FractionalIdeal.mem_singleton_mul.mpr ⟨β, hβA, rfl⟩
  · rw [hβa, mul_div_cancel_left₀ _ ht]
    exact ha

end NormEuclidean.UniformIdealPair
