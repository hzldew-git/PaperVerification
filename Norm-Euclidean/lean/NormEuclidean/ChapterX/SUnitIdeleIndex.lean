import NormEuclidean.ChapterX.SUnitFixedPart
import NormEuclidean.ChapterX.QuadraticNormIndex
import NormEuclidean.ChapterX.SNormIndex

/-!
# S-unit norm indices inside the actual idele group

The principal embedding identifies base S-units with the intersection of
principal and S-ideles. Principal norm compatibility then identifies the
actual S-unit norm index with the principal S-norm relative index in 65:13.
The exact numerical S-unit norm index remains a separate theorem.
-/

noncomputable section

namespace NormEuclidean.SUnitIdeleIndex

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open SUnitNormFiniteness PrincipalNormComponents
open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Principal embedding restricted to the actual S-unit group. -/
def principalSUnits (S : Set (HeightOneSpectrum (𝓞 K))) :
    sUnitSubgroup S →* NumberFieldIdele K :=
  idelePrincipalEmbedding.comp (sUnitSubgroup S).subtype

/-- The principal embedding is injective, as seen at any infinite component. -/
theorem principal_injective : Function.Injective (idelePrincipalEmbedding (K := K)) := by
  intro x y h
  let v : NumberField.InfinitePlace K := Classical.choice inferInstance
  apply Units.ext
  apply (algebraMap K v.Completion).injective
  exact congrArg (fun i ↦ (ideleInfiniteComponent v i).val) h

/-- Actual S-units are exactly principal S-ideles. -/
theorem principalSUnits_range (S : Set (HeightOneSpectrum (𝓞 K))) :
    (principalSUnits S).range = idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S := by
  ext i
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.val, rfl⟩, ?_⟩
    exact (sUnitSubgroup_eq_comap S).le x.property
  · rintro ⟨⟨x, rfl⟩, hx⟩
    have hs : x ∈ sUnitSubgroup S := (sUnitSubgroup_eq_comap S).ge hx
    exact ⟨⟨x, hs⟩, rfl⟩

/-- The principal S-norm subgroup is the image of the actual S-unit norm range. -/
theorem principal_norm_image (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (normSUnits theta htheta S).range.map (principalSUnits S) =
      principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  ext i
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨idelePrincipalEmbedding x.val, ⟨⟨x.val, rfl⟩, ?_⟩, ?_⟩
    · exact (sUnitSubgroup_eq_comap
        (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S)).le x.property
    · exact QuadraticPrincipalNorm.principal_norm theta htheta x.val
  · rintro ⟨_, ⟨⟨x, rfl⟩, hx⟩, rfl⟩
    have hs : x ∈ sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) :=
      (sUnitSubgroup_eq_comap _).ge hx
    let z : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) := ⟨x, hs⟩
    refine ⟨normSUnits theta htheta S z, ⟨z, rfl⟩, ?_⟩
    exact (QuadraticPrincipalNorm.principal_norm theta htheta x).symm

/-- The literal principal S-norm index in 65:13 is the actual S-unit norm index. -/
theorem principal_norm_index_eq (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
      (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) =
        (normSUnits theta htheta S).range.index := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let f := principalSUnits S
  have hf : Function.Injective f := principal_injective.comp (sUnitSubgroup S).subtype_injective
  have h := Subgroup.index_comap
    (principalSNormSubgroup (E := QuadraticAlgebra K theta.val 0) S) f
  rw [← principal_norm_image theta htheta S, Subgroup.comap_map_eq,
    MonoidHom.ker_eq_bot f hf, sup_bot_eq, principalSUnits_range] at h
  rw [principal_norm_image theta htheta S] at h
  exact h.symm

/-- The local side of 65:13 is now the proved explicit power of two on
every admissible common core. No exact S-unit index value is asserted. -/
theorem exists_core_numeric_balance (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∃ S : Set (HeightOneSpectrum (𝓞 K)), ∃ hS : Sᶜ.Finite,
      Disjoint S T ∧
      (sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
        (idelePrincipalEmbedding.range ⊓ finitePlaceSIdeleSubgroup S) *
          (idelePrincipalEmbedding.range ⊔ (extensionIdeleNorm (K := K)
            (E := QuadraticAlgebra K theta.val 0)).range).index =
        2 ^ SNormIndex.nonsplitCount theta S hS := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  obtain ⟨S, hS, _, hdis, htwo, hunit, hprincipal⟩ :=
    exists_admissible_common_core (E := QuadraticAlgebra K theta.val 0) theta T hT
  refine ⟨S, hS, hdis, ?_⟩
  exact (QuadraticNormIndex.local_global_balance theta htheta S
    (hprincipal S le_rfl).1 (hprincipal S le_rfl).2).trans
      (SNormIndex.index_eq_pow theta htheta S hS htwo hunit)

end NormEuclidean.SUnitIdeleIndex
