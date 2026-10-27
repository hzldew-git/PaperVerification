import NormEuclidean.NumberFieldNorm
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Actual finite fractional-ideal class representatives

Number-field ideal-class finiteness supplies finitely many actual nonzero
fractional ideals. Every nonzero fractional ideal is a nonzero principal
multiple of one representative. A finite family of nonzero fractional ideals
also has an actual common nonzero integral scalar.
-/

noncomputable section

namespace NormEuclidean.IdealClassRepresentatives

open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

local instance : Fintype (ClassGroup (integerSubring K)) :=
  inferInstanceAs (Fintype (ClassGroup (𝓞 K)))

/-- Finite ideal classes yield actual representatives and actual principal scalars. -/
theorem exists_finite_representatives :
    ∃ s : Finset (FractionalIdeal (integerSubring K)⁰ K), (∀ A ∈ s, A ≠ 0) ∧
      ∀ I : FractionalIdeal (integerSubring K)⁰ K, I ≠ 0 →
        ∃ A ∈ s, ∃ t : K, t ≠ 0 ∧ I = FractionalIdeal.spanSingleton (integerSubring K)⁰ t * A := by
  classical
  let R := integerSubring K
  let f : ClassGroup R → (FractionalIdeal R⁰ K)ˣ := fun ξ ↦
    FractionalIdeal.mk0 K (Classical.choose (ClassGroup.mk0_surjective ξ))
  have hf (ξ : ClassGroup R) : ClassGroup.mk K (f ξ) = ξ := by
    rw [ClassGroup.mk_mk0]
    exact Classical.choose_spec (ClassGroup.mk0_surjective ξ)
  let s := Finset.univ.image fun ξ ↦ (f ξ : FractionalIdeal R⁰ K)
  refine ⟨s, ?_, ?_⟩
  · intro A hA
    obtain ⟨ξ, _, rfl⟩ := Finset.mem_image.mp hA
    exact Units.ne_zero _
  · intro I hI
    let U := Units.mk0 I hI
    let ξ := ClassGroup.mk K U
    let A := f ξ
    let W := U * A⁻¹
    have hW : ClassGroup.mk K W = 1 := by
      change ClassGroup.mk K (U * (f ξ)⁻¹) = 1
      rw [map_mul, map_inv, hf]
      exact mul_inv_cancel ξ
    have hp : ((W : FractionalIdeal R⁰ K) : Submodule R K).IsPrincipal :=
      ClassGroup.mk_eq_one_iff.mp hW
    obtain ⟨t, ht⟩ := hp.principal
    have hfrac : (W : FractionalIdeal R⁰ K) = FractionalIdeal.spanSingleton R⁰ t := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact ht
    have ht0 : t ≠ 0 := by
      intro hzero
      apply Units.ne_zero W
      rw [hfrac, hzero, FractionalIdeal.spanSingleton_zero]
    refine ⟨A, Finset.mem_image.mpr ⟨ξ, Finset.mem_univ ξ, rfl⟩, t, ht0, ?_⟩
    have hprod : (W : FractionalIdeal R⁰ K) * A = I := by
      change (U * A⁻¹ : (FractionalIdeal R⁰ K)ˣ).val * A.val = U.val
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [← hfrac, hprod]

/-- Any finite family of nonzero fractional ideals has a common nonzero
integral element. This requires neither prime ideals nor a principal ideal ring. -/
theorem exists_common_nonzero_integer
    (s : Finset (FractionalIdeal (integerSubring K)⁰ K)) (hs : ∀ I ∈ s, I ≠ 0) :
    ∃ β : integerSubring K, β ≠ 0 ∧ ∀ I ∈ s, (β : K) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert I s hI ih =>
      obtain ⟨β, hβ, hβs⟩ := ih (fun J hJ ↦ hs J (Finset.mem_insert_of_mem hJ))
      obtain ⟨a, ha, haI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger
        (hs I (Finset.mem_insert_self I s))
      change (a : K) ∈ (I : Submodule (integerSubring K) K) at haI
      refine ⟨a * β, mul_ne_zero ha hβ, ?_⟩
      intro J hJ
      rcases Finset.mem_insert.mp hJ with hJI | hJ
      · rw [hJI]
        change (a : K) * (β : K) ∈ (I : Submodule (integerSubring K) K)
        simpa only [Subring.smul_def, smul_eq_mul, mul_comm]
          using (I : Submodule (integerSubring K) K).smul_mem β haI
      · change (a : K) * (β : K) ∈ (J : Submodule (integerSubring K) K)
        simpa only [Subring.smul_def, smul_eq_mul]
          using (J : Submodule (integerSubring K) K).smul_mem a (hβs J hJ)

end NormEuclidean.IdealClassRepresentatives
