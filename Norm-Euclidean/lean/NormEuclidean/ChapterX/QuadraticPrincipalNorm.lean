import NormEuclidean.ChapterX.QuadraticCompletedFactorization
import NormEuclidean.ChapterX.PrincipalNormComponents

/-!
# Full principal idele compatibility for quadratic number fields

The finite comparison now includes split places. Together with the proved
infinite comparison this gives equality of full ideles, not only of selected
components. The principal norm images in the S-idele constructions can
therefore be identified with actual principal global field norms.
-/

noncomputable section

namespace NormEuclidean.QuadraticPrincipalNorm

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm PrincipalNormComponents
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The full quadratic idele norm commutes with the principal embedding,
at all finite and infinite places, without local square conditions. -/
theorem principal_norm (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ x : (QuadraticAlgebra K (theta : K) 0)ˣ,
      extensionIdeleNorm (K := K) (idelePrincipalEmbedding x) =
        idelePrincipalEmbedding (globalNormUnits (K := K) x) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro x
  apply Units.ext
  apply Prod.ext
  · funext v
    exact congrArg Units.val (infinite_principal_norm v x)
  · apply DFunLike.ext
    intro p
    exact congrArg Units.val (finite_principal_norm_of_injective p
      (QuadraticCompletedFactorization.comparison_injective theta htheta p) x)

/-- Equality of the two homomorphisms on global extension units. -/
theorem principal_norm_hom (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K (theta : K) 0)).comp
        idelePrincipalEmbedding = idelePrincipalEmbedding.comp (globalNormUnits (K := K)) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply MonoidHom.ext
  intro x
  exact principal_norm theta htheta x

/-- Norms of principal extension ideles are exactly principal global field norms. -/
theorem principal_norm_range (theta : Kˣ) (htheta : ¬ IsSquare theta) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ((extensionIdeleNorm (K := K) (E := QuadraticAlgebra K (theta : K) 0)).comp
        idelePrincipalEmbedding).range =
      (idelePrincipalEmbedding.comp
        (globalNormUnits (K := K) (E := QuadraticAlgebra K (theta : K) 0))).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [principal_norm_hom theta htheta]

/-- The actual principal S-norm subgroup consists of principal global field norms. -/
theorem principalSNorm_le_global (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    principalSNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S ≤
      (idelePrincipalEmbedding.comp
        (globalNormUnits (K := K) (E := QuadraticAlgebra K (theta : K) 0))).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [← principal_norm_range theta htheta]
  exact (principalSNormSubgroup_le S).trans inf_le_right

/-- Both literal containments in the principal S-idele intersection are proved
for the actual quadratic extension S-norm subgroup. -/
theorem principalSNorm_le_intersection (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    principalSNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S ≤
      (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) ⊓
        sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro i hi
  have hS := (principalSNormSubgroup_le S hi).1
  have hglobal := principalSNorm_le_global theta htheta S hi
  obtain ⟨x, hx⟩ := hglobal
  refine ⟨⟨?_, (sIdeleNormSubgroup_le S hS).1⟩, hS⟩
  exact ⟨globalNormUnits (K := K) x, hx⟩

/-- Source principalization now gives generation by actual principal global norms
and actual extension S-idele norms. No norm-index identity is assumed. -/
theorem norm_range_generation (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    idelePrincipalEmbedding.range ⊔
        finitePlaceSIdeleSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K (theta : K) 0) S)
          = ⊤ →
      (idelePrincipalEmbedding.comp
        (globalNormUnits (K := K) (E := QuadraticAlgebra K (theta : K) 0))).range ⊔
        sIdeleNormSubgroup (E := QuadraticAlgebra K (theta : K) 0) S =
          (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K (theta : K) 0)).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro hS
  rw [← principal_norm_range theta htheta]
  exact norm_range_of_extension_principalization S hS

end NormEuclidean.QuadraticPrincipalNorm
