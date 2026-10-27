import NormEuclidean.AdelicComparison
import NormEuclidean.ChapterX.QuadraticGlobalNormIndex
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The ordinary class kernel in the full idele group

Infinite components are unrestricted. The kernel is the product of actual
principal ideles and finite valuation-unit ideles, and its index is the
ordinary ideal class number. No class-field existence theorem is assumed.
-/

noncomputable section

namespace NormEuclidean.FullIdeleClassKernel

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The finite projection with the canonical ring-of-integers algebra structure. -/
def finiteProjection : NumberFieldIdele K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (RingHom.snd (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing (𝓞 K) K)).toMonoidHom

/-- The ordinary ideal class map on actual full ideles. -/
def classHom : NumberFieldIdele K →* ClassGroup (𝓞 K) :=
  FiniteIdele.classHom.comp finiteProjection

/-- All finite components are valuation units; infinite components are arbitrary. -/
def unitIdeles : Subgroup (NumberFieldIdele K) :=
  FiniteIdele.localUnitSubgroup.comap finiteProjection

@[simp] theorem classHom_principal (k : Kˣ) :
    classHom (idelePrincipalEmbedding k) = 1 :=
  FiniteIdele.classHom_diagonal k

/-- Every ordinary ideal class is represented by an actual full idele. -/
theorem classHom_surjective : Function.Surjective (classHom (K := K)) := by
  intro c
  obtain ⟨a, ha⟩ := FiniteIdele.classHom_surjective (R := 𝓞 K) (K := K) c
  exact ⟨AdelicComparison.fullOfFiniteIdele a, ha⟩

/-- An ordinary principal ideal class gives an actual principal-times-unit decomposition. -/
theorem exists_principal_mul_unit (i : NumberFieldIdele K) (hi : classHom i = 1) :
    ∃ k : Kˣ, ∃ u : unitIdeles (K := K), i = idelePrincipalEmbedding k * u.1 := by
  obtain ⟨k, u, hu⟩ := FiniteIdele.exists_diagonal_mul_localUnit_of_classHom_eq_one
    (finiteProjection i) hi
  let j := (idelePrincipalEmbedding k)⁻¹ * i
  have hj : j ∈ unitIdeles := by
    change finiteProjection j ∈ FiniteIdele.localUnitSubgroup
    have he : finiteProjection j = u.1 := by
      dsimp only [j]
      rw [map_mul, map_inv]
      change (FiniteAdeleRing.unitEmbedding (𝓞 K) K k)⁻¹ *
        finiteProjection i = u.1
      rw [hu, inv_mul_cancel_left]
    exact he.symm ▸ u.2
  exact ⟨k, ⟨j, hj⟩, by simp [j]⟩

/-- The full ordinary class kernel uses all infinite components, including real signs. -/
theorem ker_eq : (classHom (K := K)).ker =
    idelePrincipalEmbedding.range ⊔ unitIdeles := by
  apply le_antisymm
  · intro i hi
    obtain ⟨k, u, hu⟩ := exists_principal_mul_unit i hi
    rw [hu]
    exact Subgroup.mul_mem_sup ⟨k, rfl⟩ u.2
  · apply sup_le
    · rintro _ ⟨k, rfl⟩
      exact classHom_principal k
    · intro i hi
      exact FiniteIdele.classHom_eq_one_of_localUnit hi

/-- The full ordinary idelic class index is the actual ordinary field class number. -/
theorem kernel_index : (classHom (K := K)).ker.index = NumberField.classNumber K := by
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective classHom
      classHom_surjective).toEquiv, Nat.card_eq_fintype_card]
  rfl

/-- Equal finite indices force equality of nested subgroups. -/
theorem eq_of_le_of_index_eq {G : Type*} [Group G] {A B : Subgroup G}
    (hle : A ≤ B) (hindex : A.index = B.index) (hfinite : B.index ≠ 0) : A = B := by
  have hmul := Subgroup.relIndex_mul_index hle
  rw [hindex] at hmul
  have hr : A.relIndex B = 1 :=
    (Nat.mul_right_cancel (Nat.pos_of_ne_zero hfinite)
      (hmul.trans (one_mul B.index).symm))
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hr)

/-- A quadratic norm group containing every unit idele is exactly the ordinary
class kernel after adjoining principal ideles when the ordinary class number is two. -/
theorem principal_norm_eq_kernel (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hclass : NumberField.classNumber K = 2)
    (hunit : unitIdeles ≤ (QuadraticExtensionNorm.quadraticExtensionIdeleNorm
      theta htheta).range) :
    idelePrincipalEmbedding.range ⊔
      (QuadraticExtensionNorm.quadraticExtensionIdeleNorm theta htheta).range =
        (classHom (K := K)).ker := by
  have hle : (classHom (K := K)).ker ≤ idelePrincipalEmbedding.range ⊔
      (QuadraticExtensionNorm.quadraticExtensionIdeleNorm theta htheta).range := by
    rw [ker_eq]
    exact sup_le_sup_left hunit _
  have hnorm : (idelePrincipalEmbedding.range ⊔
      (QuadraticExtensionNorm.quadraticExtensionIdeleNorm theta htheta).range).index = 2 :=
    QuadraticGlobalNormIndex.index_two theta htheta
  exact (eq_of_le_of_index_eq hle ((kernel_index.trans hclass).trans hnorm.symm)
    (hnorm.trans_ne (by decide))).symm

end NormEuclidean.FullIdeleClassKernel
